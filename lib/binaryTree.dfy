include "../lib/seq.dfy"

module BinaryTree {
import opened Seq
datatype Tree = Node(val: int, left: Tree, right: Tree) | Nil

function TreePreorderTraversal(root: Tree): seq<Tree>
    // ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil
    // ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil && (x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right))
    // ensures forall x :: x in root.repr ==> x in PreorderTraversal(root)
    // ensures injectiveSeq(TreePreorderTraversal(root))
    // ensures forall k :: 0 <= k < |TreePreorderTraversal(root)| ==> TreePreorderTraversal(root)[k] in root.repr
    // ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> forall child :: child in PreorderTraversal(root)[k].repr && child != child in PreorderTraversal(root)[k] ==> exists j :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
{
   if root == Nil then [] else if root.left != Nil && root.right != Nil then [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right) else if root.left != Nil then [root]+TreePreorderTraversal(root.left) else if root.right != Nil then [root]+TreePreorderTraversal(root.right) else [root]
}

predicate validTree(root: Tree) {
    if root != Nil then root.left != root && root.right != root && (forall lchild :: lchild in TreePreorderTraversal(root.left) ==> lchild != root && lchild !in TreePreorderTraversal(root.right)) && (forall rchild :: rchild in TreePreorderTraversal(root.right) ==> rchild != root && rchild !in TreePreorderTraversal(root.left)) && validTree(root.right) && validTree(root.left) else true
    // if root != Nil then root.left != root && root.right != root && root !in TreePreorderTraversal(root.left)  && root !in TreePreorderTraversal(root.right) && forall x :: x in TreePreorderTraversal(root.left) ==> x !in TreePreorderTraversal(root.right) && forall x :: x in TreePreorderTraversal(root.right) ==> x !in TreePreorderTraversal(root.left) && validTree(root.right) && validTree(root.left) else true
}

lemma rootNotInChildren(root: Tree)
    requires root != Nil
    requires validTree(root);
    ensures root != Nil && root.left != Nil ==> root !in TreePreorderTraversal(root.left)
    ensures root != Nil && root.right != Nil ==> root !in TreePreorderTraversal(root.right)
{
    assert root in TreePreorderTraversal(root);
    tpt(root);
    if root != Nil && root.left != Nil && root.right != Nil {
        calc {
            TreePreorderTraversal(root);
            [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right);
        }
        assert root !in TreePreorderTraversal(root.left);
    }else{

    }
}

lemma {:verify } TPTInjective(root: Tree) 
    requires validTree(root)
    requires root != Nil
    ensures distinct(TreePreorderTraversal(root))
{
    NoNil(root);
    tpt(root);
    assert root !in TreePreorderTraversal(root.left);
    assert root !in TreePreorderTraversal(root.right);
    if root.right != Nil && root.left != Nil {
        calc{
            TreePreorderTraversal(root);
            [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right);
        }
        TPTInjective(root.left);
        TPTInjective(root.right);
        distincts([root], TreePreorderTraversal(root.left));
        distincts([root] + TreePreorderTraversal(root.left), TreePreorderTraversal(root.right));

    }else if root.right != Nil {
        calc{
            TreePreorderTraversal(root);
            [root]+TreePreorderTraversal(root.right);
        }
        TPTInjective(root.right);
        distincts([root], TreePreorderTraversal(root.right));
    }else if root.left != Nil {

        calc{
            TreePreorderTraversal(root);
            [root]+TreePreorderTraversal(root.left);
        }
        TPTInjective(root.left);
        distincts([root], TreePreorderTraversal(root.left));
    }
}

lemma NoNil(root: Tree)
    ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil
{

}

lemma tpt(root: Tree)
    ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil
    ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil && (x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right))
{

}


lemma AllChildTraversalElementsInRoot(root: Tree, elem: Tree)
    requires elem in TreePreorderTraversal(root)
    ensures forall child :: child in TreePreorderTraversal(elem) ==> child in TreePreorderTraversal(root)
{

}

lemma TreePreorderTraversalSubstrings(root: Tree)
    requires root != Nil
    ensures root.left != Nil ==> isSubstring(TreePreorderTraversal(root.left), TreePreorderTraversal(root))
    ensures root.right != Nil ==> isSubstring(TreePreorderTraversal(root.right), TreePreorderTraversal(root))
{
   if root.left != Nil && root.right != Nil {
    calc {
        TreePreorderTraversal(root);
        [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right);
    }
    var k := 1;
    var j := |TreePreorderTraversal(root.left)|+1;
    assert 0 <= k <= j <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root.left) == TreePreorderTraversal(root)[1..|TreePreorderTraversal(root.left)|+1];

    var s := 1+|TreePreorderTraversal(root.left)|;
    var t := |TreePreorderTraversal(root)|;
    assert 0 <= s <= t <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root.right) == TreePreorderTraversal(root)[s..t];
   }else if root.left != Nil && root.right == Nil {
    calc {
        TreePreorderTraversal(root);
        [root]+TreePreorderTraversal(root.left);
    }
    var k := 1;
    var j := |TreePreorderTraversal(root.left)|+1;
    assert 0 <= k <= j <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root.left) == TreePreorderTraversal(root)[1..j];
   }else if root.left == Nil && root.right != Nil {
    calc {
        TreePreorderTraversal(root);
        [root]+TreePreorderTraversal(root.right);
    }
    var k := 1;
    var j := |TreePreorderTraversal(root.right)|+1;
    assert 0 <= k <= j <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root.right) == TreePreorderTraversal(root)[1..j];
   }
}

lemma AllContained(root: Tree)
    requires root != Nil
    ensures forall x :: x in TreePreorderTraversal(root) ==> (x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right))
{
}

lemma {:verify true} {:induction false} AllChildrenTraversalsAreSubstrings(root: Tree) 
    requires root != Nil
    ensures forall x ::x in TreePreorderTraversal(root) ==> isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root))
{
    NoNil(root);
    AllContained(root);
    forall x | x in TreePreorderTraversal(root) 
        ensures isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root))
    {
        tpt(root);
        if x == root {
            var k, j := 0, |TreePreorderTraversal(root)|;
            assert 0 <= k <= j <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root) == TreePreorderTraversal(root)[k..j];
        }else if x == root.left || x == root.right {
           TreePreorderTraversalSubstrings(root); 
        }else {
            if root.left != Nil && root.right != Nil {
                assert x != root;
                assert TreePreorderTraversal(root) == [root] + TreePreorderTraversal(root.left) + TreePreorderTraversal(root.right);
                if root.left != Nil  && x in TreePreorderTraversal(root.left) {
                    AllChildrenTraversalsAreSubstrings(root.left);
                    assert isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root.left));
                    TreePreorderTraversalSubstrings(root);
                    AllSubstringsAreSubstrings(TreePreorderTraversal(x), TreePreorderTraversal(root.left), TreePreorderTraversal(root));
                }
                if root.right != Nil && x in TreePreorderTraversal(root.right) {
                    AllChildrenTraversalsAreSubstrings(root.right);
                    assert isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root.right));
                    TreePreorderTraversalSubstrings(root);
                    AllSubstringsAreSubstrings(TreePreorderTraversal(x), TreePreorderTraversal(root.right), TreePreorderTraversal(root));
                }
            }else if root.left != Nil  && x in TreePreorderTraversal(root.left) {
                AllChildrenTraversalsAreSubstrings(root.left);
                assert isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root.left));
                    TreePreorderTraversalSubstrings(root);
                    AllSubstringsAreSubstrings(TreePreorderTraversal(x), TreePreorderTraversal(root.left), TreePreorderTraversal(root));
            }else  if root.right != Nil && x in TreePreorderTraversal(root.right) {
                AllChildrenTraversalsAreSubstrings(root.right);
                    assert isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root.right));
                    TreePreorderTraversalSubstrings(root);
                    AllSubstringsAreSubstrings(TreePreorderTraversal(x), TreePreorderTraversal(root.right), TreePreorderTraversal(root));
            }else{
                assert x != root;
                assert x !in TreePreorderTraversal(root.left);
                assert x !in TreePreorderTraversal(root.right);
                assert false;
            }
        }
    }
}

lemma TreeChildrenAreLater(root: Tree)
    requires root != Nil
    ensures forall x :: x in TreePreorderTraversal(root) && x != root ==> exists k:nat :: 0 < k < |TreePreorderTraversal(root)| && TreePreorderTraversal(root)[k] == x
{
    NoNil(root);
}

lemma {:verify true} TreePreorderTraversalChildrenAreLater3(root: Tree, elem: Tree, k: nat) 
    // requires validTree(root)
    requires distinct(TreePreorderTraversal(root))
    requires k < |TreePreorderTraversal(root)|
    requires elem in TreePreorderTraversal(root)
    requires elem != Nil
    requires TreePreorderTraversal(root)[k] == elem
    ensures forall child :: child in TreePreorderTraversal(elem) && child != elem ==> exists j: nat :: k < j < |TreePreorderTraversal(root)| && TreePreorderTraversal(root)[j] == child
{
    // TPTInjective(root);
    AllChildTraversalElementsInRoot(root, elem);
    AllChildrenTraversalsAreSubstrings(root);
    AllChildrenTraversalsAreSubstrings(elem);
    TreeChildrenAreLater(elem);
    forall child | child in TreePreorderTraversal(elem) && child != elem
        ensures exists j: nat :: k < j < |TreePreorderTraversal(root)| && TreePreorderTraversal(root)[j] == child
    {
        assert child in TreePreorderTraversal(root);
        assert child != elem;
        var j:nat :| 0 < j < |TreePreorderTraversal(elem)| && TreePreorderTraversal(elem)[j] == child;
        var s,t :| 0 <= s < t <= |TreePreorderTraversal(root)| && TreePreorderTraversal(elem) == TreePreorderTraversal(root)[s..t];
        assert TreePreorderTraversal(root)[k] == elem;
        assert TreePreorderTraversal(elem)[0] == elem;
        assert TreePreorderTraversal(root)[s] == elem;
        assert s == k;
        assert TreePreorderTraversal(root)[s+j] == child;

        // seqbusiness(TreePreorderTraversal(root), child);
        // var j :| 0 <= j < |TreePreorderTraversal(root)| && TreePreorderTraversal(root)[j] == child;
        // assert isSubstring(TreePreorderTraversal(child), TreePreorderTraversal(elem));
        // AllSubstringsAreSubstrings(TreePreorderTraversal(child), TreePreorderTraversal(elem), TreePreorderTraversal(root));
        // assert isSubstring(TreePreorderTraversal(child), TreePreorderTraversal(root));
        // // assert |TreePreorderTraversal(child)| <= |TreePreorderTraversal(elem)|;
        // var s,t :| 0 <= s < t <= |TreePreorderTraversal(root)| && TreePreorderTraversal(child) == TreePreorderTraversal(root)[s..t];
        // assert j == s;
    }
}
}