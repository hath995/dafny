/**
 * https://leetcode.com/problems/invert-binary-tree/description/
 * Definition for a binary tree node.
 class TreeNode {
     val: number
     left: TreeNode | null
     right: TreeNode | null
     constructor(val?: number, left?: TreeNode | null, right?: TreeNode | null) {
         this.val = (val===undefined ? 0 : val)
         this.left = (left===undefined ? null : left)
         this.right = (right===undefined ? null : right)
     }
 }

function invertTree(root: TreeNode | null): TreeNode | null {
    if(root == null) return null;
    let leftChild = invertTree(root.left);
    let rightChild = invertTree(root.right);
    root.right = leftChild;
    root.left = rightChild;
    return root;
};
 */
include "../lib/seq.dfy"
import opened Seq
class TreeNode {
    var val: int;
    var left: TreeNode?;
    var right: TreeNode?;
    ghost var repr: set<TreeNode>;

    constructor(val: int, left: TreeNode?, right: TreeNode?)
        requires left != null ==> left.Valid()
        requires right != null ==> right.Valid()
        requires left != null && right != null ==> left.repr !! right.repr
        ensures this.val == val
        ensures this.left == left
        ensures this.right == right
        ensures left != null ==> this !in left.repr
        ensures right != null ==> this !in right.repr
        ensures Valid()
    {
        this.val := val;
        this.left := left;
        this.right := right;
        var leftRepr := if left != null then {left}+left.repr else {};
        var rightRepr := if right != null then {right}+right.repr else {};
        this.repr := {this} + leftRepr + rightRepr;
    }

    predicate Valid()
        reads this, repr
        decreases repr
    {
        this in repr &&
        (this.left != null ==>
        (this.left in repr
        && this !in this.left.repr
        && this.left.repr < repr
        && this.left.Valid()
        ))
        && (this.right != null ==>
        (this.right in repr
        && this !in this.right.repr
        && this.right.repr < repr
        && this.right.Valid())) &&
        (this.left != null && this.right != null ==> this.left.repr !! this.right.repr && this.repr == {this} + this.left.repr + this.right.repr)
        && (this.left != null && this.right == null ==> this.repr == {this} + this.left.repr)
        && (this.right != null && this.left == null ==> this.repr == {this} + this.right.repr)
        && (this.right == null && this.left == null ==> this.repr == {this})
    }

    predicate iterativeValid()
        reads this, repr
        decreases repr
        requires this.Valid()
    {
        forall x :: x in PreorderTraversal(this) ==> x in repr
    }

    method  invertBinaryTree() returns (newRoot: TreeNode?)
        modifies this.repr
        requires this.Valid()
        ensures newRoot == this && newRoot.right == old(this.left) && newRoot.left == old(this.right)
        ensures newRoot.repr == old(this.repr) && newRoot.Valid()
        ensures forall node :: node in this.repr ==> node.right == old(node.left) && node.left == old(node.right)
        decreases repr
    {
        var leftChild: TreeNode? := null;
        if left != null {
            leftChild := left.invertBinaryTree();
        }
        var rightChild: TreeNode? := null;
        if right != null {
            rightChild := right.invertBinaryTree();
        }
        right := leftChild;
        left := rightChild;
        return this;
    }


}

datatype Tree = Node(val: int, left: Tree, right: Tree) | Nil

predicate injectiveSeq<A>(s: seq<A>) {
    forall x,y :: x != y && 0 <= x < y < |s| ==> s[x] != s[y]
}

function method PreorderTraversal(root: TreeNode): seq<TreeNode>
    reads root.repr
    requires root.Valid()
    // ensures forall x :: x in PreorderTraversal(root) ==> x.Valid()
    ensures forall x :: x in root.repr ==> x in PreorderTraversal(root)
    ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> PreorderTraversal(root)[k] in root.repr && PreorderTraversal(root)[k].Valid()
    ensures injectiveSeq(PreorderTraversal(root))
    ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> PreorderTraversal(root)[k] in root.repr
    // ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> forall child :: child in PreorderTraversal(root)[k].repr && child != child in PreorderTraversal(root)[k] ==> exists j :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
{
   if root.left != null && root.right != null then [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right) else if root.left != null then [root]+PreorderTraversal(root.left) else if root.right != null then [root]+PreorderTraversal(root.right) else [root]
}

function method TreePreorderTraversal(root: Tree): seq<Tree>
    // ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil
    // ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil && (x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right))
    // ensures forall x :: x in root.repr ==> x in PreorderTraversal(root)
    // ensures injectiveSeq(TreePreorderTraversal(root))
    // ensures forall k :: 0 <= k < |TreePreorderTraversal(root)| ==> TreePreorderTraversal(root)[k] in root.repr
    // ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> forall child :: child in PreorderTraversal(root)[k].repr && child != child in PreorderTraversal(root)[k] ==> exists j :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
{
   if root == Nil then [] else if root.left != Nil && root.right != Nil then [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right) else if root.left != Nil then [root]+TreePreorderTraversal(root.left) else if root.right != Nil then [root]+TreePreorderTraversal(root.right) else [root]
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
    // tpt(root);
    // NoNil(root);
    // forall x | x in TreePreorderTraversal(root)
    //     ensures x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right)
    // {
    //     assert x != Nil;
    //     if x == root {

    //     }else if root.left != Nil && root.right != Nil {
    //         calc {
    //             TreePreorderTraversal(root);
    //             [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right);
    //         }
    //         assert x in [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right);
    //         assert x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right);
    //     }else if root.left == Nil && root.right != Nil {
    //         calc {
    //             TreePreorderTraversal(root);
    //             [root]+TreePreorderTraversal(root.right);
    //         }
    //         assert x in [root]+TreePreorderTraversal(root.right);
    //         assert x in TreePreorderTraversal(root.right);
    //     }else if root.left != Nil && root.right == Nil {
    //         calc {
    //             TreePreorderTraversal(root);
    //             [root]+TreePreorderTraversal(root.left);
    //         }
    //         assert x in [root]+TreePreorderTraversal(root.left);
    //         assert x in TreePreorderTraversal(root.left);
    //     }else{
    //         assert false;
    //     }

    // }
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

lemma {:verify false} PreorderTraversalSubstrings(root: TreeNode)
    requires root.Valid()
    ensures root.left != null ==> isSubstring(PreorderTraversal(root.left), PreorderTraversal(root))
    ensures root.right != null ==> isSubstring(PreorderTraversal(root.right), PreorderTraversal(root))
{

   if root.left != null && root.right != null {
    calc {
        PreorderTraversal(root);
        [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
    }
    var k := 1;
    var j := |PreorderTraversal(root.left)|+1;
    assert 0 <= k <= j <= |PreorderTraversal(root)| && PreorderTraversal(root.left) == PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1];

    var s := 1+|PreorderTraversal(root.left)|;
    var t := |PreorderTraversal(root)|;
    assert 0 <= s <= t <= |PreorderTraversal(root)| && PreorderTraversal(root.right) == PreorderTraversal(root)[s..t];
   }else if root.left != null && root.right == null {
    calc {
        PreorderTraversal(root);
        [root]+PreorderTraversal(root.left);
    }
    var k := 1;
    var j := |PreorderTraversal(root.left)|+1;
    assert 0 <= k <= j <= |PreorderTraversal(root)| && PreorderTraversal(root.left) == PreorderTraversal(root)[1..j];
   }else if root.left == null && root.right != null {
    calc {
        PreorderTraversal(root);
        [root]+PreorderTraversal(root.right);
    }
    var k := 1;
    var j := |PreorderTraversal(root.right)|+1;
    assert 0 <= k <= j <= |PreorderTraversal(root)| && PreorderTraversal(root.right) == PreorderTraversal(root)[1..j];
   }
}

// lemma AllChildrenTraversalsAreSubstrings(root: TreeNode) 
//     requires root.Valid()
//     ensures forall x :: x in root.repr && x in PreorderTraversal(root) ==> isSubstring(PreorderTraversal(x), PreorderTraversal(root))
// {
//     forall x | x in root.repr && x in PreorderTraversal(root) 
//         ensures isSubstring(PreorderTraversal(x), PreorderTraversal(root))
//     {
//         if x == root {

//         }else if x == root.left || x == root.right {
//            PreorderTraversalSubstrings(root); 
//         }else {
//             if root.left != null && x in root.left.repr {
//                 AllChildrenTraversalsAreSubstrings(root.left);
//             }
//             if root.right != null && x in root.right.repr {
//                 AllChildrenTraversalsAreSubstrings(root.right);
//             }
//         }
//     }
// }

predicate seqElement<A>(s: seq<A>, elem: A, k: nat)

{
    0 <= k < |s| && elem in s && s[k] == elem
}

lemma {:verify } PreorderTraversalChildrenAreLater1(root: TreeNode)
    requires root.Valid()
    //would not verify until asserted that x was also in PreorderTraversal(root)
    ensures forall x :: x in root.repr && x in PreorderTraversal(root) ==> exists k: nat :: 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
{
    forall x | x in root.repr 
        ensures exists k: nat :: 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
    {
        assert x in PreorderTraversal(root);
        seqbusiness(PreorderTraversal(root), x);
    }
}

lemma {:verify true} PreorderTraversalChildrenAreLater(root: TreeNode)
    requires root.Valid()
    //the following does not verify
    ensures forall x :: x in root.repr && x in PreorderTraversal(root) && x != root ==> exists k: nat :: 0 < k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
{
    
    // forall x | x in root.repr && x in PreorderTraversal(root) && x != root
        // ensures exists k: nat :: 0 < k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
    // {
        // PreorderTraversalChildrenAreLater1(root);
        // var k :| 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x;
        // assert PreorderTraversal(root)[0] == root;
    // }
    // but it verifies here, at least I get the green checkmark
    // assert forall x :: x in root.repr ==> exists k: nat :: 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x;
}

lemma {:verify false} TreePreorderTraversalChildrenAreLater3(root: Tree, elem: Tree, k: nat) 
    requires elem in TreePreorderTraversal(root)
    requires TreePreorderTraversal(root)[k] == elem
    // ensures forall child :: child in TreePreorderTraversal(elem) && child in PreorderTraversal(root) && child != elem ==> exists j: nat :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
{

}



lemma {:verify false} PreorderTraversalChildrenAreLater3(root: TreeNode, elem: TreeNode, k: nat) 
    requires root.Valid()
    requires elem in root.repr
    requires elem in PreorderTraversal(root)
    requires PreorderTraversal(root)[k] == elem
    // ensures forall child :: child in elem.repr && child in PreorderTraversal(root) && child != elem ==> exists j: nat :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
{

}

lemma seqbusiness<A>(s: seq<A>, elem: A)
    requires elem in s
    ensures exists k:nat :: 0 <= k < |s| && s[k] == elem
    ensures exists k:nat :: seqElement(s, elem, k) 
{
    assert elem in s;
    assert exists k:nat :: 0 <= k < |s| && s[k] == elem && seqElement(s, elem, k);
}

method swapChildren(root: TreeNode) returns (newRoot: TreeNode)
    modifies root
    requires root.Valid()
    ensures root == newRoot && newRoot.Valid()
    ensures root.right == old(root.left) && root.left == old(root.right)
    ensures forall x :: x in root.repr && x != root ==> unchanged(x)
{

    var temp := root.left;
    root.left := root.right;
    root.right := temp;
    return root;
}

method  invertBinaryTree(root: TreeNode?) returns (newRoot: TreeNode?)
    modifies if root != null then root.repr else {}
    requires root != null ==> root.Valid()
    ensures root == null ==> newRoot == null
    ensures root != null ==> newRoot != null && newRoot.repr == old(root.repr) && newRoot.Valid()
    ensures root != null ==> newRoot == root && newRoot.right == old(root.left) && root.left == old(root.right)
    ensures root != null ==> forall node :: node in newRoot.repr ==> node.right == old(node.left) && node.left == old(node.right)
    decreases if root == null then {} else root.repr
{
    if root != null {
        var leftChild := null;
        if root.left != null {
            leftChild := invertBinaryTree(root.left);
        }
        var rightChild := root.right;
        if root.right != null  {
            rightChild := invertBinaryTree(root.right);
        }
        root.right := leftChild;
        root.left := rightChild;
        return root;
    }else{
        return null;
    }
}

lemma ChildNodesAreInRoot(root: TreeNode, child: TreeNode)
    requires root.Valid()
    requires (root.left != null && child == root.left) || (root.right != null && root.right == child)
    ensures child in root.repr;
{

}

lemma ChildChildrenNodesAreInRoot(root: TreeNode, child: TreeNode)
    requires root.Valid()
    requires (root.left != null && (child == root.left.left || child == root.left.right)) || (root.right != null && (root.right.left == child || root.right.right == child))
    ensures child in root.repr;
{

}

lemma ChildNodesAreValid(root: TreeNode, child: TreeNode)
    requires root.Valid()
    requires child in root.repr;
    decreases root.repr
    ensures child.repr <= root.repr;
    ensures child.Valid()
{
    if child == root {
    }else if child == root.left {

    }else if child == root.right {

    }else if root.left != null && root.right != null {
        assert root.repr == {root} + root.left.repr + root.right.repr;
        if child in root.left.repr {
            ChildNodesAreValid(root.left, child);
        }else if child in root.right.repr {
            ChildNodesAreValid(root.right, child);
        }else{
            assert false;
        }
    }else if root.right != null {

    }else if root.left != null {

    }else{
        assert false;
    }
}

twostate lemma ValidSwappingStillValid(root: TreeNode, child: TreeNode)
    requires root.Valid()
    requires child in root.repr;
    requires child.left == old(child.right) && child.right == old(child.left)
    ensures root.Valid()
{
    ChildNodesAreValid(root,child);
    assert child.Valid();
}

function TreeUnion(nodes: seq<TreeNode>): set<TreeNode>
    reads set x | 0 <= x < |nodes| :: nodes[x]
{
   if |nodes| > 0 then nodes[0].repr + TreeUnion(nodes[1..]) else {}
}
//fresh ensures that a variable was initialized by a method or two-state function

method {:verify false} invertBinaryTreeIterative1(root: TreeNode?) returns (newRoot: TreeNode?)
    modifies if root != null then root.repr else {}
    requires root != null ==> root.Valid()
    ensures root == null ==> newRoot == null
    ensures root != null ==> newRoot == root && newRoot.repr == old(root.repr)
    // ensures root != null ==> newRoot != null && newRoot.repr == old(root.repr) && newRoot.Valid()
    // ensures root != null ==> forall node :: node in newRoot.repr ==> node.right == old(node.left) && node.left == old(node.right)
    // ensures root != null ==> newRoot == root && newRoot.right == old(root.left) && root.left == old(root.right)
{
    if root == null {
        return null;
    }

    var nodes := PreorderTraversal(root);
    assert forall k :: 0 <= k < |nodes| ==> nodes[k] in root.repr && nodes[k].Valid();
    ghost var visited: set<TreeNode> := {};
    ghost var unvisited: set<TreeNode> := root.repr;
    var i := 0;
    while i < |nodes| 
        modifies root.repr
        invariant 0 <= i <= |nodes|
        invariant root.repr == old(root.repr)
        invariant forall k::i < k <= |nodes| ==> unchanged(nodes[k])
    //     // invariant visited == set k | k < i < |nodes| :: nodes[k]
    //     invariant forall x :: x in nodes ==> x.Valid()
    //     // invariant root.Valid()
    //     // invariant forall k :: 0<= k < i ==> nodes[k].right == old(nodes[k].left) && nodes[k].left == old(nodes[k].right)
    {
        assert nodes[i] in nodes;
        assert nodes[i] in root.repr;
        assert nodes[i].Valid();
    // //     var temp := nodes[i].left;
    // //     nodes[i].left := nodes[i].right;
    // //     nodes[i].right := temp;
        nodes[i].left, nodes[i].right := nodes[i].right, nodes[i].left;
        assert nodes[i].right == old(nodes[i].left) && nodes[i].left == old(nodes[i].right);
    // //     // var newNode := swapChildren(nodes[i]);
    // //     ValidSwappingStillValid(root, nodes[i]);
    // //     visited := visited + {nodes[i]};
        i := i + 1;
    }
    return root;
}

method {:verify false} invertBinaryTreeIterative(root: TreeNode?) returns (newRoot: TreeNode?)
    modifies if root != null then root.repr else {}
    requires root != null ==> root.Valid()
    ensures root == null ==> newRoot == null
    // ensures root != null ==> newRoot != null && newRoot.repr == old(root.repr) && newRoot.Valid()
    // ensures root != null ==> newRoot == root && newRoot.right == old(root.left) && root.left == old(root.right)
    ensures newRoot.repr == old(root.repr)
    ensures root != null ==> newRoot == root
    // ensures root != null ==> forall node :: node in newRoot.repr ==> node.right == old(node.left) && node.left == old(node.right)
{
    if root == null {
        return null;
    }
    assert root != null;
    assert root.Valid();
    var stack: seq<TreeNode> := [root];
    ghost var visited: set<TreeNode> := {};
    ghost var unvisited: set<TreeNode> := root.repr;
    assert TreeUnion(stack) == unvisited;
    assert TreeUnion(stack) == root.repr - visited;
    assert root in root.repr;
    assert root.repr <= root.repr;
    assert root in stack;
    while |stack| > 0 
        modifies root.repr
        invariant root.Valid()
        invariant root.repr == old(root.repr)
        invariant forall x :: x in stack ==> x in root.repr;
        invariant forall x :: x in unvisited ==> unchanged(x)
        // invariant forall x :: x in stack ==> x.Valid() && x.repr <= root.repr;
        invariant visited + unvisited == root.repr;
        // invariant visited == visited + {stack[0]}
        // invariant TreeUnion(stack) == root.repr - visited
        invariant forall node :: node in visited ==> node.right == old(node.left) && node.left == old(node.right) && node.Valid()
        decreases unvisited
    {
        var current: TreeNode := stack[0];
        assert current in stack;
        ChildNodesAreValid(root, current);
        if current.left != null {
            assert current.left.repr <= root.repr;
            assert current.left in root.repr;
            ChildNodesAreValid(root, current.left);
            stack :=  stack + [current.left];
        }
        if current.right != null {
            assert current.right.repr <= root.repr;
            assert current.right in root.repr;
            ChildNodesAreValid(root, current.right);
            stack := stack + [current.right];
        }
        var temp := current.left;
        current.left := current.right;
        current.right := temp;
        assert temp == old(current.left);
        assert current.left == old(current.right) && current.right == old(current.left);
        ValidSwappingStillValid(root, current);
        visited := visited + {current};
        unvisited := unvisited - {current};
        stack := stack[1..];
    }
    return root;
}
        // assert root.right == old(root.left) && root.left == old(root.right);
        // if root.right != null && root.left != null {
        //     assert root.repr == {root} + root.left.repr + root.right.repr;
        //     assert forall node :: node in root.right.repr ==> node.right == old(node.left) && node.left == old(node.right);
        //     assert forall node :: node in root.left.repr ==> node.right == old(node.left) && node.left == old(node.right);
        // }else if root.right != null && root.left == null {
        //     assert root.repr == {root}  + root.right.repr;
        //     assert forall node :: node in root.right.repr ==> node.right == old(node.left) && node.left == old(node.right);
        // }else if root.right == null && root.left != null {
        //     assert root.repr == {root}  + root.left.repr;
        //     assert forall node :: node in root.left.repr ==> node.right == old(node.left) && node.left == old(node.right);
        // }else{
        //     assert root.left == null;
        //     assert root.right == null;
        // }
        // if root.right != null {
        //     assert old(root.left) != null;
        //     // assert old(root.left).repr < old(root.repr);
        //     assert root.repr == old(root.repr);
        //     assert root.right.repr == old(root.left).repr;
        //     // assert root.right.repr < root.repr;
        // }