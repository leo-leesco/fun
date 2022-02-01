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
    fn new() -> Self {
        Leaf
    }
}

impl<K: Ord, V: Copy> BST<K, V> {
    fn find_copy_rec(&self, k: K) -> Option<V> {
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

    fn find_copy(&self, k: K) -> Option<V> {
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
    fn find_rec<'a>(&'a self, k: K) -> Option<&'a V> {
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

    fn find<'a>(&'a self, k: K) -> Option<&'a V> {
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

    fn find_mut_rec<'a>(&'a mut self, k: K) -> Option<&'a mut V> {
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

    fn find_mut<'a>(&'a mut self, k: K) -> Option<&'a mut V> {
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

    fn insert<'a>(&'a mut self, k: K, v: V) -> Option<V> {
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

struct IntoIter<K, V> {
    cur: BST<K, V>,
    stack: Vec<(K, V, BST<K, V>)>
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
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
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter{ cur: self, stack: vec![] }
    }
}

struct Iter<'a, K, V> {
    cur: &'a BST<K, V>,
    stack: Vec<(&'a K, &'a V, &'a BST<K, V>)>
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
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
        while let Some(Node(b)) = self.cur.take() {
            self.stack.push((&b.key, &mut b.val, &mut b.right));
            self.cur = Some(&mut b.left)
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
