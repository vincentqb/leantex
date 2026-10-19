macro_rules! square {
    ($x:expr) => { $x * $x };
    ($($rest:tt),*) => { 0 };
}

/// A unit of work.
pub(crate) async fn work<T: Into<u64> + Send>(v: T) -> Result<u64, Box<dyn std::error::Error>> {
    let v: u64 = v.into();
    unsafe { Ok(square!(v)) }
}

const LIMIT: usize = 64;
static mut COUNT: i32 = -1;
type Pair = (i8, i8);
mod inner { pub fn f() -> &'static str { "inner" } }
struct Unit;
union Bits { i: u32, f: f32 }
extern "C" { fn abs(input: i32) -> i32; }
/* a block comment /* nested */ still a comment */
fn r#match() -> bool { true }
