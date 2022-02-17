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

    impl<T> Clone for PArray<T> {
        fn clone(&self) -> Self {
            PArray(self.0.clone())
        }
    }

    impl<T> PArray<T> {
        pub fn new(v: Vec<T>) -> Self {
            PArray(Rc::new(RefCell::new(Arr(v))))
        }

        pub fn get(&self, i: usize) -> T where T: Copy {
            self.reroot();
            self.0.borrow().get_arr()[i]
        }

        pub fn set(&self, i: usize, x: T) -> Self {
            let res = PArray(Rc::new(RefCell::new(Diff(i, x, self.clone()))));
            res.reroot();
            res
        }

        #[allow(dead_code)]
        fn reroot_rec(&self) {
            let mut bself = self.0.borrow_mut();
            if let Arr(_) = &*bself { return }
            let (i, x, next) = std::mem::replace(&mut *bself, Invalid).from_diff();
            next.reroot_rec();
            let mut bnext = next.0.borrow_mut();
            let y = std::mem::replace(&mut bnext.get_arr_mut()[i], x);
            *bself = std::mem::replace(&mut *bnext, Diff(i, y, self.clone()));
        }

        fn reroot(&self) {
            // Optimize for hot path
            if let Arr(_) = &*self.0.borrow() { return }

            let mut st = Invalid;
            let mut cur = self.clone();
            loop {
                std::mem::swap(&mut *cur.0.borrow_mut(), &mut st);
                match st {
                    Diff(_, _, ref mut next) => std::mem::swap(next, &mut cur),
                    Arr(mut vec) => {
                        loop {
                            let mut b = cur.0.borrow_mut();
                            match &mut *b {
                                Diff(i, x, next) => {
                                    std::mem::swap(x, &mut vec[*i]);
                                    let next = next.clone();
                                    drop(b);
                                    cur = next;
                                },
                                Invalid => {
                                    *b = Arr(vec);
                                    return
                                },
                                Arr(_) => panic!()
                            }
                        }
                    }
                    Invalid => panic!()
                }

            }
        }
    }
}
use parray::*;

fn test_0() {
    let arr = PArray::new(vec![0; 5]);
    let arr2 = arr.set(0, 5);
    let arr3 = arr.set(1, 42);
    assert!(arr.get(0) == 0 && arr.get(1) == 0);
    assert!(arr2.get(0) == 5 && arr2.get(1) == 0);
    assert!(arr3.get(0) == 0 && arr3.get(1) == 42);
}

fn bench_0() {
    let start = std::time::Instant::now();
    let mut a = PArray::new(vec![0; 1000]);
    let mut v = vec![];
    for i in (1..=1000_000).rev() {
        v.push(a.clone());
        a = a.set(0, i)
    }
    let res : i64 = v.iter().map(|a| a.get(0)).sum();
    let dt = start.elapsed().as_secs_f32();
    assert!(res == 500000499999);
    println!("Time: {}", dt)
}

mod nqueens {
    use PArray;

    #[derive(Clone)]
    struct Board {
        n: usize,
        tab: PArray<bool>
    }

    impl Board {
        fn pos(&self, r: usize, c: usize) -> usize {
            r * self.n + c
        }

        fn get(&self, r: usize, c: usize) -> bool {
            self.tab.get(self.pos(r, c))
        }

        fn print(&self) {
            for r in 0..self.n {
                for c in 0..self.n {
                    if self.get(r, c) { print!("X") }
                    else { print!("_") }
                }
                println!();
            }
        }

        fn is_consistent(&self, r: usize, c: usize) -> bool {
            for i in 0..self.n {
                if self.get(r, i) { return false }
            }
            for i in 0..self.n {
                if self.get(i, c) { return false }
            }
            for i in 0..self.n {
                if r >= i && c >= i && self.get(r-i, c-i) { return false }
                if r >= i && c+i < self.n && self.get(r-i, c+i) { return false }
                if r+i < self.n && c >= i && self.get(r+i, c-i) { return false }
                if r+i < self.n && c+i < self.n && self.get(r+i, c+i) { return false }
            }
            true
        }

        fn nqueens_inner(&self, col: usize) -> Option<Board> {
            if col == self.n { return Some(self.clone()) }
            for row in 0..self.n {
                if self.is_consistent(row, col) {
                    let b = Board{ tab: self.tab.set(self.pos(row, col), true), ..*self };
                    let r = b.nqueens_inner(col+1);
                    match r { Some(_) => return r, _ => () }
                }
            }
            None
        }
    }

    pub fn go(n: usize) {
        let b = Board{ n, tab: PArray::new(vec![false; n*n])};
        if let Some(b) = b.nqueens_inner(0) {
            b.print()
        }
    }
}

fn main() {
    test_0();
    bench_0();
    nqueens::go(20);
}
