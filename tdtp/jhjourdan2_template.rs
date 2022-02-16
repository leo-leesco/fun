mod parray {
    use std::cell::RefCell;
    use std::rc::Rc;

    enum PAState<T> {
        Arr(Vec<T>),
        Diff(usize, T, PArray<T>),
        Invalid
    }
    use self::PAState::*;

    pub struct PArray<T>(Rc<RefCell<PAState<T>>>);

    // impl<T> Clone for PArray<T> {
    // TODO
    // }

    impl<T> PArray<T> {
        pub fn new(v: Vec<T>) -> Self {
            // TODO
            panic!()
        }

        pub fn get(&self, i: usize) -> T where T: Copy {
            // TODO
            panic!()
        }

        pub fn set(&self, i: usize, x: T) -> Self {
            // TODO
            panic!()
        }

        fn reroot(&self) {
            // TODO
            panic!()
        }
    }
}
use parray::*;

// Uncomment the following to use the test and benchmark

// fn test_0() {
//     let arr = PArray::new(vec![0; 5]);
//     let arr2 = arr.set(0, 5);
//     let arr3 = arr.set(1, 42);
//     assert!(arr.get(0) == 0 && arr.get(1) == 0);
//     assert!(arr2.get(0) == 5 && arr2.get(1) == 0);
//     assert!(arr3.get(0) == 0 && arr3.get(1) == 42);
// }

// fn bench_0() {
//     let start = std::time::Instant::now();
//     let mut a = PArray::new(vec![0; 1000]);
//     let mut v = vec![];
//     for i in (1..=1000_000).rev() {
//         v.push(a.clone());
//         a = a.set(0, i)
//     }
//     let res : i64 = v.iter().map(|a| a.get(0)).sum();
//     let dt = start.elapsed().as_secs_f32();
//     assert!(res == 500000499999);
//     println!("Time: {}", dt)
// }

fn main() {
    // test_0();
    // bench_0();
}
