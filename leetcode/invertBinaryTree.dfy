/**
 * https://leetcode.com/problems/invert-binary-tree/description/
 * Definition for a binary tree node.
 * class TreeNode {
 *     val: number
 *     left: TreeNode | null
 *     right: TreeNode | null
 *     constructor(val?: number, left?: TreeNode | null, right?: TreeNode | null) {
 *         this.val = (val===undefined ? 0 : val)
 *         this.left = (left===undefined ? null : left)
 *         this.right = (right===undefined ? null : right)
 *     }
 * }

function invertTree(root: TreeNode | null): TreeNode | null {
    if(root == null) return null;
    let leftChild = invertTree(root.left);
    let rightChild = invertTree(root.right);
    root.right = leftChild;
    root.left = rightChild;
    return root;
};
 */

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