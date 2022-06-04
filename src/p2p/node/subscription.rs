use dashmap::DashMap;
use std::sync::Arc;
use tokio::sync::mpsc;

#[derive(Debug, Default)]
pub struct SubscriptionManager<T> {
    pub(crate) subs: Arc<DashMap<usize, mpsc::Sender<T>>>,
}

impl<T: Clone> SubscriptionManager<T> {
    pub(crate) fn new() -> Self {
        Self {
            subs: Arc::new(DashMap::new()),
        }
    }

    pub async fn send(&self, val: T) {
        for ref_multi in self.subs.iter() {
            let _ = ref_multi.value().send(val.clone()).await;
        }
    }

    pub fn subscribe(&self) -> Subscriber<T> {
        let id = self.subs.len();
        let (tx, rx) = mpsc::channel(128);
        self.subs.insert(id, tx);

        Subscriber {
            id,
            subs: self.subs.clone(),
            rx,
        }
    }
}

pub struct Subscriber<T> {
    id: usize,
    subs: Arc<DashMap<usize, mpsc::Sender<T>>>,

    rx: mpsc::Receiver<T>,
}

impl<T: std::fmt::Debug> Subscriber<T> {
    pub async fn recv(&mut self) -> Option<T> {
        self.rx.recv().await
    }
}

impl<T> Drop for Subscriber<T> {
    fn drop(&mut self) {
        assert!(self.subs.remove(&self.id).is_some());
    }
}
