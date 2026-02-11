#![allow(dead_code)]

use std::cmp::Ordering::*;

struct Node<K, V> {
    left: BST<K, V>,
    key: K,
    val: V,
    right: BST<K, V>
}

enum BST<K, V> {
    Leaf,
    Node(Box<Node<K, V>>)
}
use BST::*;

impl<K, V> BST<K, V> {
    // Question 1
    fn new() -> Self {
        Leaf
    }
}

impl<K: Ord, V: Copy> BST<K, V> {
    // Question 2
    fn find_copy_rec(&self, k: &K) -> Option<V> {
        match self {
            Leaf => None,
            Node(b) => {
                match k.cmp(&b.key) {
                    Equal => Some(b.val),
                    Less => b.left.find_copy_rec(k),
                    Greater => b.right.find_copy_rec(k)
                }
            }
        }
    }

    // Question 3
    fn find_copy(&self, k: &K) -> Option<V> {
        let mut tree = self;
        loop {
            match tree {
                Leaf => return None,
                Node(b) =>
                    match k.cmp(&b.key) {
                        Equal => return Some(b.val),
                        Less => tree = &b.left,
                        Greater => tree = &b.right
                    }
            }
        }
    }
}


impl<K: Ord, V> BST<K, V> {
    // Not required by the statement
    fn find_rec<'a, 'b>(&'a self, k: &'b K) -> Option<&'a V> {
        match self {
            Leaf => None,
            Node(b) =>
                match k.cmp(&b.key) {
                    Equal => Some(&b.val),
                    Less => b.left.find_rec(k),
                    Greater => b.right.find_rec(k)
                }
        }
    }

    // Question 4
    // The lifetime of `self` and `k` need to be different. Otherwise, the
    // borrowed variable by k cannot be used until the return value of `find`
    // is still live.
    // In particular, if we do not put lifetimes annotations here, then Rust
    // will use the same lifetime everywhere which enforces unecessary
    // constraints to the caller.
    fn find<'a, 'b>(&'a self, k: &'b K) -> Option<&'a V> {
        let mut tree = self;
        loop {
            match tree {
                Leaf => return None,
                Node(b) =>
                    match k.cmp(&b.key) {
                        Equal => return Some(&b.val),
                        Less => tree = &b.left,
                        Greater => tree = &b.right
                    }
            }
        }
    }

    // Not required by the statement
    fn find_mut_rec<'a, 'b>(&'a mut self, k: &'b K) -> Option<&'a mut V> {
        match self {
            Leaf => None,
            Node(b) =>
                match k.cmp(&b.key) {
                    Equal => Some(&mut b.val),
                    Less => b.left.find_mut_rec(k),
                    Greater => b.right.find_mut_rec(k)
                }
        }
    }

    // Not required by the statement
    fn find_mut<'a, 'b>(&'a mut self, k: &'b K) -> Option<&'a mut V> {
        let mut tree = self;
        loop {
            match tree {
                Leaf => return None,
                Node(b) =>
                    match k.cmp(&b.key) {
                        Equal => return Some(&mut b.val),
                        Less => tree = &mut b.left,
                        Greater => tree = &mut b.right
                    }
            }
        }
    }

    // Question 5
    fn insert(&mut self, k: K, v: V) -> Option<V> {
        let mut tree = self;
        loop {
            match tree {
                Leaf => {
                    *tree = Node(Box::new(
                        Node{ left: Leaf, key: k, val: v, right: Leaf }));
                    return None
                },
                Node(b) => match k.cmp(&b.key) {
                    Equal => return Some(std::mem::replace(&mut b.val, v)),
                    Less => tree = &mut b.left,
                    Greater => tree = &mut b.right
                }
            }
        }
    }
}

struct IterMove<K, V> {
    cur: BST<K, V>,
    stack: Vec<(K, V, BST<K, V>)>
}

impl<K, V> Iterator for IterMove<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        /* Here, we would actually like to write something like:
               while let Node(b) = self.cur { ... }
           and we would like to get full ownership of b.
           However, Rust's ownership discipline makes this impossible, since
           self is a borrow. Indeed, a borrow can never be "emptied", meaning it
           has to always point to a value of the required type. This is
           important because many Rust instructions can actually trigger a
           panic (e.g., by stack overflow or out of memory), which may end a
           borrow prematurely. If the borrow were emptied at that time, then
           the lender could catch the panic and see an invalid value in the
           borrowed variable.

           To solve that issue, we use std::mem::replace in order to get the
           full ownership of the content of self.cur, while leaving there a
           default value (Leaf). */
        let mut cur = std::mem::replace(&mut self.cur, Leaf);
        while let Node(b) = cur {
            self.stack.push((b.key, b.val, b.right));
            cur = b.left
        }
        match self.stack.pop() {
            None => None,
            Some((key, val, r)) => {
                self.cur = r;
                Some((key, val))
            }
        }
    }
}

impl<K, V> IntoIterator for BST<K, V> {
    type Item = (K, V);
    type IntoIter = IterMove<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IterMove{ cur: self, stack: vec![] }
    }
}

struct Iter<'a, K, V> {
    cur: &'a BST<K, V>,
    stack: Vec<(&'a K, &'a V, &'a BST<K, V>)>
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        /* Here, we do not need the std::mem::replace trick, because we only
           need (and have) a share borrow, which is Copy. So b is actually a
           shared borrow to the content of the Node, which can be extracted from
           a borrow of the iterator, without making anything invalid. */
        while let Node(b) = self.cur {
            self.stack.push((&b.key, &b.val, &b.right));
            self.cur = &b.left
        }
        match self.stack.pop() {
            None => None,
            Some((key, val, r)) => {
                self.cur = r;
                Some((key, val))
            }
        }
    }
}

impl<'a, K, V> IntoIterator for &'a BST<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        Iter{ cur: self, stack: vec![] }
    }
}

struct IterMut<'a, K, V> {
    cur: Option<&'a mut BST<K, V>>,
    stack: Vec<(&'a K, &'a mut V, &'a mut BST<K, V>)>
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        /* We have the same problem as in IterMove: we would like to
           temporarily take the content of self.cur, and keep the ownership of
           self so that we can modify the field self.cur (in the match bellow).

           However, we don't have a default value for &'a mut BST<K, V>, the
           type of self.cur! Hence, the trick here is to use
           Option<&'a mut BST<K, V>> for the type of self.cur, and to take
           ownership of self.cur by replacing by None. This is exaclty what
           self.cur.take() does: it is equivalent to
           std::mem::replace(&mut self.cur, None). Then, unwrap() simply checks
           that the returned value is of the form Some(x) and returns x. If it
           is not, then it panics.

           Note that the only performance penalty of this trick is the needless
           write to self.cur and the check performed by unwrap. In particular,
           Rust knows that Option<&'a mut BST<K, V>> can be stored in one word
           only, using 0 for the representation of None (borrows can never be
           NULL).
         */
        let mut cur = self.cur.take().unwrap();
        while let Node(b) = cur {
            self.stack.push((&b.key, &mut b.val, &mut b.right));
            cur = &mut b.left
        }
        match self.stack.pop() {
            None => None,
            Some((key, val, r)) => {
                self.cur = Some(r);
                Some((key, val))
            }
        }
    }
}

impl<'a, K, V> IntoIterator for &'a mut BST<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IterMut{ cur: Some(self), stack: vec![] }
    }
}


fn main() {

}
