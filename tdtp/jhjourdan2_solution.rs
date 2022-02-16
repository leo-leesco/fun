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
            if let Arr(v) = &*self.0.borrow() { v[i] }
            else { panic!() }
        }

        pub fn set(&self, i: usize, x: T) -> Self {
            let res = PArray(Rc::new(RefCell::new(Diff(i, x, self.clone()))));
            res.reroot();
            res
        }

        #[allow(dead_code)]
        fn reroot_rec(&self) {
            let mut bself = self.0.borrow_mut();
            match std::mem::replace(&mut *bself, Invalid) {
                Diff(i, x, next) => {
                    next.reroot();
                    let mut bnext = next.0.borrow_mut();
                    if let Arr(v) = &mut *bnext {
                        let y = std::mem::replace(&mut v[i], x);
                        *bself = std::mem::replace(&mut *bnext, Diff(i, y, self.clone()))
                    } else {
                        panic!()
                    }
                },
                Arr(v) => *bself = Arr(v),
                Invalid => panic!()
            }
        }

        fn reroot(&self) {
            let mut st = Invalid;
            let mut cur = self.clone();
            let mut vec;
            loop {
                std::mem::swap(&mut *cur.0.borrow_mut(), &mut st);
                match st {
                    Diff(_, _, ref mut next) => {
                        std::mem::swap(next, &mut cur)
                    },
                    Arr(v) => {
                        vec = v;
                        break
                    }
                    Invalid => panic!()
                }

            }
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
                        break
                    },
                    Arr(_) => panic!()
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

fn main() {
    test_0();
    bench_0();
}
