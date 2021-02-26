use once_cell::sync::Lazy;
use reqwest::blocking::Client;
use std::time::Duration;

pub mod download;
mod query;

static HTTP_CLIENT: Lazy<Client> = Lazy::new(|| {
    Client::builder()
        .connect_timeout(Duration::from_millis(150))
        .timeout(Duration::from_secs(30))
        .pool_max_idle_per_host(5)
        .build()
        .expect("Failed to build Reqwest Client")
});

