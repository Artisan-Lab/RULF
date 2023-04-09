// edition:2018
// revisions: no_drop_tracking drop_tracking
// [drop_tracking] check-pass
// [drop_tracking] compile-flags: -Zdrop-tracking=yes
// [no_drop_tracking] compile-flags: -Zdrop-tracking=no
use std::any::Any;
use std::future::Future;

struct Client(Box<dyn Any + Send>);

impl Client {
    fn status(&self) -> u16 {
        200
    }
}

async fn get() {}

pub fn foo() -> impl Future + Send {
    //[no_drop_tracking]~^ ERROR future cannot be sent between threads safely
    let client = Client(Box::new(true));
    async move {
        match client.status() {
            200 => {
                let _x = get().await;
            }
            _ => (),
        }
    }
}

fn main() {}
