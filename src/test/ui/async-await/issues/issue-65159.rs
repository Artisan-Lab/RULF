// Regression test for #65159. We used to ICE.
//
// edition:2018

async fn copy() -> Result<()>
//~^ ERROR this enum takes 2 generic arguments
{
    Ok(())
    //~^ ERROR type annotations needed
}

fn main() { }
