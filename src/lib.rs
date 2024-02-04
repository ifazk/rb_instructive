use std::{cell::RefCell, cmp::Ord, fmt::Debug, rc::Rc};

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum Color {
    Red,
    Black,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum RBSide {
    Left,
    Right,
}

impl RBSide {
    fn other(self) -> Self {
        match self {
            RBSide::Left => RBSide::Right,
            RBSide::Right => RBSide::Left,
        }
    }
}

type BareTree<K, T> = Rc<RefCell<Node<K, T>>>;
type Tree<K, T> = Option<BareTree<K, T>>;

pub struct Node<K: Ord, T> {
    color: Color,
    key: K,
    value: T,
    parent: Tree<K, T>,
    child_of_parent: Option<RBSide>,
    left: Tree<K, T>,
    right: Tree<K, T>,
}

impl<K: Ord + Debug, T> std::fmt::Debug for Node<K, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("color", &self.color)
            .field("key", &self.key)
            .field("left", &self.left)
            .field("right", &self.right)
            .finish()
    }
}

impl<K: Ord, T> Node<K, T> {
    pub fn new(key: K, value: T) -> BareTree<K, T> {
        Rc::new(RefCell::new(Node {
            color: Color::Red,
            key: key,
            value: value,
            parent: None,
            child_of_parent: None,
            left: None,
            right: None,
        }))
    }

    fn get_child(&self, child: RBSide) -> Tree<K, T> {
        match child {
            RBSide::Left => self.left.clone(),
            RBSide::Right => self.right.clone(),
        }
    }

    fn take_child(&mut self, child: RBSide) -> Tree<K, T> {
        match child {
            RBSide::Left => self.left.take(),
            RBSide::Right => self.right.take(),
        }
    }

    // Shallow set parent, does not modify parent node
    fn set_parent(&mut self, child_of_parent: RBSide, parent: BareTree<K, T>) {
        self.parent = Some(parent);
        self.child_of_parent = Some(child_of_parent);
    }

    // Shallow set child, does not modify child node
    fn set_child(&mut self, side: RBSide, child: Tree<K, T>) {
        match side {
            RBSide::Left => self.left = child,
            RBSide::Right => self.right = child,
        }
    }
}

pub struct RBTree<K: Ord, T> {
    root: Tree<K, T>,
    pub length: usize,
}

impl<K: Ord, T> Drop for RBTree<K, T> {
    fn drop(&mut self) {
        fn nullify_parent<K: Ord,T>(x: Tree<K, T>) {
            if let Some(r) = x {
                r.borrow_mut().parent = None;
            }
        }
        self.walk(nullify_parent);
    }
}

impl<K: Ord, T> RBTree<K, T> {
    pub fn walk(&self, f: impl Fn(Tree<K,T>) -> ()) {
        self.in_order(&self.root, &f)
    }

    fn in_order(&self, node: &Tree<K,T>, f: &impl Fn(Tree<K,T>) -> ()) {
        if let Some(r) = node.as_ref() {
            self.in_order(&r.borrow().left, f);
        }
        f(node.clone());
        if let Some(r) = node.as_ref() {
            self.in_order(&r.borrow().right, f);
        }
    }
}

impl<K: Ord + Copy, T: Clone> RBTree<K, T> {
    pub fn new() -> RBTree<K, T> {
        RBTree {
            root: None,
            length: 0,
        }
    }

    pub fn add(&mut self, key: K, value: T) {
        self.length += 1;
        let root = self.root.take();
        let (_new_rooted, new_node) = self.add_r(root, key, value);
        self.root = self.fix_tree(new_node)
    }

    pub fn get_root_key(&self) -> Option<K> {
        self.root.as_ref().map(|x| x.borrow().key)
    }

    pub fn get_root_value(&self) -> Option<T> {
        self.root.as_ref().map(|x| x.borrow().value.clone())
    }

    // returns clone of value
    pub fn find(&self, key: K) -> Option<T> {
        self.find_r(&self.root, key)
    }

    fn find_r(&self, node: &Tree<K, T>, key: K) -> Option<T> {
        match node.as_ref() {
            None => None,
            Some(node_rc) => match node_rc.borrow().key.cmp(&key) {
                std::cmp::Ordering::Equal => Some(node_rc.borrow().value.clone()),
                std::cmp::Ordering::Greater => self.find_r(&node_rc.borrow().left, key),
                std::cmp::Ordering::Less => self.find_r(&node_rc.borrow().right, key),
            },
        }
    }

    fn insert_side(&self, subroot_key: K, insert_key: K) -> RBSide {
        if subroot_key <= insert_key {
            RBSide::Right
        } else {
            RBSide::Left
        }
    }

    // The .0 BareTree is the new sub-tree
    // The .1 BareTree is the newly inserted node
    fn add_r(&mut self, node: Tree<K, T>, key: K, value: T) -> (BareTree<K, T>, BareTree<K, T>) {
        match node {
            None => {
                let new = Node::new(key, value);
                (new.clone(), new)
            }
            Some(n) => {
                let current_key = n.borrow().key;
                let insert_side = self.insert_side(current_key, key);

                // Insert into insert_side
                let old_child_subtree = n.borrow_mut().take_child(insert_side);
                let (new_child_subtree, inserted_node) = self.add_r(old_child_subtree, key, value);

                new_child_subtree
                    .borrow_mut()
                    .set_parent(insert_side, n.clone());
                n.borrow_mut()
                    .set_child(insert_side, Some(new_child_subtree));
                (n, inserted_node)
            }
        }
    }

    // should only be called nodes where the parent is red, i.e. grand parent exists
    fn uncle(&self, node: &BareTree<K, T>) -> (RBSide, Tree<K, T>) {
        let node_ref = node.borrow();
        let parent = node_ref.parent.as_ref().unwrap();
        let parent = parent.borrow();
        let other_side = parent.child_of_parent.unwrap().other();
        let grand_parent = parent.parent.as_ref().unwrap();
        let uncle = grand_parent.borrow().get_child(other_side);
        (other_side, uncle)
    }

    // only called on non-root (red) nodes, so parent can be unwrapped
    fn parent_color(&self, node: &BareTree<K, T>) -> Color {
        let node_ref = node.borrow();
        let parent = node_ref.parent.as_ref().unwrap();
        let parent_ref = parent.borrow();
        parent_ref.color
    }

    // must have non-nil child at child_side
    // if child_side if left, performs a right rotation, and left rotation otherwise
    // Before:
    // | grand_parent
    // |      \
    // |       parent
    // |      /    \ (child_side)
    // |     a     child
    // |            /  \
    // |  grand_child   b
    // After:
    // | grand_parent
    // |        \
    // |       child
    // |        /  \
    // |   parent   b
    // |     /  \ (child_side)
    // |    a    grand_child
    fn rotate(&self, child_side: RBSide, parent: BareTree<K, T>) {
        let mut parent_mut = RefCell::borrow_mut(&parent);
        let other_side = child_side.other();

        let child_rc = parent_mut.get_child(child_side).unwrap();
        {
            // scope for borrowing child_rc
            let mut child = RefCell::borrow_mut(&child_rc);

            let grand_parent = parent_mut.parent.take();
            let child_of_grand_parent = parent_mut.child_of_parent.take();
            if let Some((gp, c)) = grand_parent.as_ref().zip(child_of_grand_parent) {
                gp.borrow_mut().set_child(c, Some(child_rc.clone()));
            }

            let grand_child = child.take_child(other_side);
            if let Some(gc) = grand_child.as_ref() {
                gc.borrow_mut().set_parent(child_side, parent.clone())
            }
            parent_mut.set_child(child_side, grand_child);

            child.parent = grand_parent;
            child.child_of_parent = child_of_grand_parent;
            child.set_child(child_side.other(), Some(parent.clone()));
        }
        parent_mut.set_parent(other_side, child_rc);
    }

    // The only violations are red-red edges or root is red
    // Cases for red-red:
    // 1. Uncle is red
    //    Make grandparent red, uncle and parent black, continue with grand-parent.
    // 2. Uncle is black (uncle subtree delta)
    //    Node+parent proper subtrees alpha, beta, gamma
    //    a. Node-parent is different from parent-grandparent
    //       Rotate to reduce to case b.
    //    b. Node-parent is same as parent-grandparent
    //       Rotate to make subtree rooted at parent, with node and grandparent
    //       children, and further subtrees alpha, beta, gamma, delta
    fn fix_tree(&mut self, inserted: BareTree<K, T>) -> Tree<K, T> {
        let mut not_root = inserted.borrow().parent.is_some();
        let root: BareTree<K, T> = if not_root {
            let mut n: BareTree<K, T> = Rc::clone(&inserted);
            let mut parent_is_red = self.parent_color(&inserted) == Color::Red;
            // n is red
            while parent_is_red && not_root {
                // parent_is_red implies grand_parent exists and is black
                let (uncle_side, uncle) = self.uncle(&n);
                let mut parent = n.borrow().parent.as_ref().unwrap().clone();
                if uncle.is_some() && uncle.as_ref().unwrap().borrow().color == Color::Red {
                    // uncle red
                    let uncle = uncle.unwrap();
                    parent.borrow_mut().color = Color::Black;
                    uncle.borrow_mut().color = Color::Black;
                    let grand_parent = parent.borrow().parent.as_ref().unwrap().clone();
                    grand_parent.borrow_mut().color = Color::Red;
                    n = grand_parent;
                } else {
                    // uncle is black
                    let parent_side = uncle_side.other();
                    let node_side = parent.borrow().child_of_parent.unwrap();
                    if node_side != parent_side {
                        // rotate to make parent of child of node
                        self.rotate(node_side, parent.clone());
                        {
                            let temp = parent;
                            parent = n;
                            n = temp;
                        }
                    };
                    // parent (currently red) will replace black grand_parent
                    parent.borrow_mut().color = Color::Black;
                    let grand_parent = RefCell::borrow(&parent).parent.clone().unwrap();
                    grand_parent.borrow_mut().color = Color::Red;
                    self.rotate(parent_side, grand_parent);
                }
                not_root = n.borrow().parent.is_some();
                parent_is_red = not_root && { self.parent_color(&n) == Color::Red }
            }
            // this climb feels excessive, feels better to climb _newly_rooted
            // in RBTree::add() but leaving it here since log(n)
            while not_root {
                let temp = n.borrow().parent.clone().unwrap();
                not_root = temp.borrow().parent.is_some();
                n = temp;
            }
            n
        } else {
            inserted
        };
        RefCell::borrow_mut(&root).color = Color::Black;
        Some(root)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rotate_1() {
        /* Input
        2 -> 4 -> 5
        |    |
        v    v
        1    3
         */
        /* Output
        4 -> 5
        |
        v
        2 -> 3
        |
        v
        1
         */
        // Setup
        // Allocate
        let orig_root = Node::new(2, ());
        let left = Node::new(1, ());
        let right = Node::new(4, ());
        let right_left = Node::new(3, ());
        let right_right = Node::new(5, ());

        // set edeges
        orig_root
            .borrow_mut()
            .set_child(RBSide::Left, Some(left.clone()));
        left.borrow_mut()
            .set_parent(RBSide::Left, orig_root.clone());

        orig_root
            .borrow_mut()
            .set_child(RBSide::Right, Some(right.clone()));
        right
            .borrow_mut()
            .set_parent(RBSide::Right, orig_root.clone());

        right
            .borrow_mut()
            .set_child(RBSide::Left, Some(right_left.clone()));
        right_left
            .borrow_mut()
            .set_parent(RBSide::Left, right.clone());

        right
            .borrow_mut()
            .set_child(RBSide::Right, Some(right_right.clone()));
        right_right
            .borrow_mut()
            .set_parent(RBSide::Right, right.clone());

        // Create RBTree
        let mut tree = RBTree::new();
        tree.root = Some(orig_root.clone());
        tree.length = 5;

        assert!(RefCell::borrow(&orig_root.clone()).parent.is_none());

        // Run
        tree.rotate(RBSide::Right, orig_root.clone());

        // test output
        assert!(orig_root.borrow().parent.is_some());
        {
            let orig_root = orig_root.clone();
            let cell = RefCell::borrow_mut(&orig_root);
            assert_eq!(cell.child_of_parent, Some(RBSide::Left));
            assert!(cell.parent.is_some());
            let parent = cell.parent.clone().unwrap();
            let parent = RefCell::borrow(&parent);
            assert_eq!(parent.key, 4);

            assert!(cell.left.is_some());
            let left_child = cell.left.clone().unwrap();
            let left_child = RefCell::borrow(&left_child);
            assert_eq!(left_child.key, 1);

            assert!(cell.right.is_some());
            let right_child = cell.right.clone().unwrap();
            let right_child = RefCell::borrow(&right_child);
            assert_eq!(right_child.key, 3);
        }

        {
            let cell = right.borrow();
            assert!(cell.child_of_parent.is_none());
            assert!(cell.parent.is_none());

            assert!(cell.left.is_some());
            let left_child = cell.left.clone().unwrap();
            let left_child = RefCell::borrow(&left_child);
            assert_eq!(left_child.key, 2);

            assert!(cell.right.is_some());
            let right_child = cell.right.clone().unwrap();
            let right_child = RefCell::borrow(&right_child);
            assert_eq!(right_child.key, 5);
        }
    }

    #[test]
    fn test_create_1() {
        // Setup
        let mut tree = RBTree::new();

        // Run
        tree.add(1, 11);
        tree.add(2, 12);
        tree.add(3, 13);
        tree.add(4, 14);
        tree.add(5, 15);

        // test output
        assert!(tree.root.is_some());
        assert_eq!(tree.length, 5);
        // would be unbalanced if these are false
        assert!(tree.get_root_key() != Some(5));
        assert!(tree.get_root_key() != Some(1));
    }

    #[test]
    fn test_find_1() {
        // Setup
        let mut tree = RBTree::new();

        // Run
        tree.add(1, 11);
        tree.add(2, 12);
        tree.add(3, 13);
        tree.add(4, 14);
        tree.add(5, 15);

        // test output
        assert!(tree.root.is_some());
        assert_eq!(tree.length, 5);
        assert_eq!(tree.find(1), Some(11));
        assert_eq!(tree.find(2), Some(12));
        assert_eq!(tree.find(3), Some(13));
        assert_eq!(tree.find(4), Some(14));
        assert_eq!(tree.find(5), Some(15));
        assert_eq!(tree.find(6), None);
    }
}
