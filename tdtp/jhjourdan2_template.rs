mod parray {
    use std::cell::RefCell;
    use std::rc::Rc;

    enum PAState<T> {
        Arr(Vec<T>),
        Diff(usize, T, PArray<T>),
        Invalid
    }
    use self::PAState::*;

    impl<T> PAState<T> {
        fn get_arr(&self) -> &Vec<T> {
            if let Arr(v) = self { v } else { panic!() }
        }

        fn get_arr_mut(&mut self) -> &mut Vec<T> {
            if let Arr(v) = self { v } else { panic!() }
        }

        fn from_diff(self) -> (usize, T, PArray<T>) {
            if let Diff(i, x, a) = self { (i, x, a) } else { panic!() }
        }
    }

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

// mod nqueens {
//     use PArray;

//     #[derive(Clone)]
//     struct Board {
//         n: usize,
//         tab: PArray<bool>
//     }

//     impl Board {
//         fn pos(&self, r: usize, c: usize) -> usize {
//             r * self.n + c
//         }

//         fn get(&self, r: usize, c: usize) -> bool {
//             self.tab.get(self.pos(r, c))
//         }

//         fn print(&self) {
//             for r in 0..self.n {
//                 for c in 0..self.n {
//                     if self.get(r, c) { print!("X") }
//                     else { print!("_") }
//                 }
//                 println!();
//             }
//         }

//         fn is_consistent(&self, r: usize, c: usize) -> bool {
//             for i in 0..self.n {
//                 if self.get(r, i) { return false }
//             }
//             for i in 0..self.n {
//                 if self.get(i, c) { return false }
//             }
//             for i in 0..self.n {
//                 if r >= i && c >= i && self.get(r-i, c-i) { return false }
//                 if r >= i && c+i < self.n && self.get(r-i, c+i) { return false }
//                 if r+i < self.n && c >= i && self.get(r+i, c-i) { return false }
//                 if r+i < self.n && c+i < self.n && self.get(r+i, c+i) { return false }
//             }
//             true
//         }

//         fn nqueens_inner(&self, col: usize) -> Option<Board> {
//             if col == self.n { return Some(self.clone()) }
//             for row in 0..self.n {
//                 if self.is_consistent(row, col) {
//                     let b = Board{ tab: self.tab.set(self.pos(row, col), true), ..*self };
//                     let r = b.nqueens_inner(col+1);
//                     match r { Some(_) => return r, _ => () }
//                 }
//             }
//             None
//         }
//     }

//     pub fn go(n: usize) {
//         let b = Board{ n, tab: PArray::new(vec![false; n*n])};
//         if let Some(b) = b.nqueens_inner(0) {
//             b.print()
//         }
//     }
// }

fn main() {
    // test_0();
    // bench_0();
    // nqueens::go(20);
}
