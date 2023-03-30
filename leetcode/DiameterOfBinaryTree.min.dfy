//https://leetcode.com/problems/diameter-of-binary-tree/description/

/*
function diameter(node: TreeNode | null): [number, number] {
  if(node == null) {
    return [-1,-1];
  }
  if(node.left == null && node.right == null) {
    return [0, 0];
  }
  let leftDiameter = diameter(node.left);
  let rightDiameter = diameter(node.right);
  let height = Math.max(leftDiameter[0],rightDiameter[0]) + 1;
  let dim = leftDiameter[0]+rightDiameter[0]+2;
  let maxDiameter = Math.max(leftDiameter[1], rightDiameter[1], dim);
  return [height, maxDiameter];
}

function diameterOfBinaryTree(root: TreeNode | null): number {
  return diameter(root)[1];
};
*/
include "../lib/seq.dfy"
include "../lib/binaryTree.dfy"
module TreeDiameter {
import opened BinaryTree
import opened Seq

function max(left: int, right: int): int {
    if left > right then left else right
}

function TreeSet(root: Tree): set<Tree> {
    match root {
        case Nil => {}
        case Node(val, left, right) => {root}+TreeSet(left)+TreeSet(right)
    }
}

function TreeHeight(root: Tree): int 
    ensures TreeHeight(root) >= -1
{
    if root == Nil then -1 else if root.left == Nil && root.right == Nil then 0 else max(TreeHeight(root.left), TreeHeight(root.right)) + 1
}

predicate isChild(a: Tree, b: Tree) {
    a != Nil && (a.left == b || a.right == b)
}

predicate isParentOrChild(a: Tree, b: Tree) {
    //a != Nil && b != Nil && (a.left == b || a.right == b || (a == b.left || a == b.right))
    a != Nil && b != Nil && (isChild(a, b) || isChild(b, a))
}

predicate isTreePath(path: seq<Tree>, start: Tree, end: Tree) {
    if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else match path[0] {
        case Nil => false
        case Node(val, left, right) => path[0] == start && path[|path|-1] == end && isParentOrChild(path[0], path[1]) && isTreePath(path[1..], path[1], end)
    }
}

predicate isTreePathAlt(path: seq<Tree>, start: Tree, end: Tree) {
    if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else path[0] == start && start != Nil && end == path[|path|-1] == end && forall i :: 0 <= i < |path| - 1 ==> isParentOrChild(path[i], path[i+1])
}

lemma TreeHeightMax(root: Tree) 
    ensures forall node :: node in TreeSet(root) ==> TreeHeight(root) >= TreeHeight(node)
{}

lemma TreePathsAreTheSameAlt(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires isTreePath(path, start, end)
    ensures isTreePathAlt(path, start, end)
{

}

lemma TreePathsAreTheSame(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires isTreePathAlt(path, start, end)
    ensures isTreePath(path, start, end)
{

}

predicate isDescTreePath(path: seq<Tree>, start: Tree, end: Tree) {
    if |path| == 0 then false else if |path| == 1 then match path[0] {
            case Nil => false
            case Node(val, left, right) => path[0] == start && end == start
    } else match path[0] {
        case Nil => false
        case Node(val, left, right) => end != Nil && path[|path|-1] == end && path[0] == start && path[1] != Nil && ((left == path[1] && isDescTreePath(path[1..],left, end)) || (right == path[1] && isDescTreePath(path[1..], right, end)))
    }
}

lemma DescPathChildren(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| > 1
    requires isDescTreePath(path, start, end)
    ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
{
}

lemma DescPathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| > 1
    requires path[0] == start;
    requires path[|path|-1] == end;
    requires forall i :: 0 <= i < |path| ==> path[i] != Nil
    requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
    ensures isDescTreePath(path, start, end)
{
}

lemma TreePathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree) 
    requires start != Nil
    requires end != Nil
    requires |path| >= 1
    requires path[0] == start;
    requires path[|path|-1] == end;
    requires forall i :: 0 <= i < |path| ==> path[i] != Nil
    requires forall i :: 0 <= i < |path| - 1 ==> isParentOrChild(path[i], path[i+1])
    ensures isTreePath(path, start, end)
{

}

lemma DescPathChildrenReverse(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| > 1
    requires isDescTreePath(path, start, end)
    ensures forall i :: 0 <= i < |reverse(path)| - 1 ==> isChild(reverse(path)[i+1], reverse(path)[i])
{
    DescPathChildren(path, start, end);
    ReverseIndexAll(path);
}

lemma AscPathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| > 1
    requires path[0] == start;
    requires path[|path|-1] == end;
    requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i+1], path[i])
    ensures isAscTreePath(path, start, end)
{
}

predicate isAscTreePath(paths: seq<Tree>, start: Tree, end: Tree) {
    if |paths| == 0 then false else if |paths| == 1 then match paths[0] {
        case Nil => false
        case Node(val, left, right) => start == paths[0] && end == start
    } else match paths[0] {
        case Nil => false
        case Node(val, left, right) => end != Nil && paths[|paths|-1] == end && start == paths[0] && paths[1] != Nil  && ((paths[0] == paths[1].left && isAscTreePath(paths[1..], paths[1], end)) || (paths[0] == paths[1].right && isAscTreePath(paths[1..], paths[1], end)))
    }
}

lemma AscPathChildren(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| > 1
    requires isAscTreePath(path, start, end)
    ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i+1], path[i])
{
}

ghost predicate ChildrenAreSeparate(root: Tree) {
    // root != Nil && forall node :: node in TreeSet(root) && node != Nil ==> TreeSet(node.left) !! TreeSet(node.right)
    root == Nil || (root != Nil && (TreeSet(root.left) !! TreeSet(root.right)) && ChildrenAreSeparate(root.left) && ChildrenAreSeparate(root.right))
}

lemma TreeSetChildInTreeSet(root: Tree, child: Tree) 
    requires root != Nil
    requires child != Nil && child in TreeSet(root)
    ensures TreeSet(child) <= TreeSet(root)
{}

lemma parentNotInTreeSet(parent: Tree, root: Tree)
    requires parent != Nil && parent != root && (parent.left == root || parent.right == root)
    ensures parent !in TreeSet(root)
{
    if root == Nil {} else {
        assert TreeSet(root) == {root}+TreeSet(root.left)+TreeSet(root.right);
        parentNotInTreeSet(root, root.left);
        parentNotInTreeSet(root, root.right);
        if parent in TreeSet(root.left) {
            TreeSetChildInTreeSet(root.left, parent);
        }else if parent in TreeSet(root.right) {
            TreeSetChildInTreeSet(root.right, parent);
        }
    }
}

method TestPath() {
    var rootleaf := Node(4, Nil, Nil);
    var leaf := Node(3, Nil, Nil);
    var child := Node(2, Nil, leaf);
    var root := Node(1, child, rootleaf);

    var test := Node(10, rootleaf, rootleaf);
    //should this be allowed?
    assert isTreePath([rootleaf, root, rootleaf], rootleaf, rootleaf);
    // assert isPath([leaf, child, root, rootleaf]);
    assert !isTreePath([root, rootleaf], leaf, rootleaf);
    assert isTreePath([leaf, child, root], leaf, root);
    assert isTreePath([root, rootleaf], root, rootleaf);
    assert isTreePath([leaf, child, root, rootleaf], leaf, rootleaf);
    assert isDescTreePath([root, child, leaf], root, leaf);
    assert !isDescTreePath([root], root, leaf);
    assert isDescTreePath([root, rootleaf],root, rootleaf);
    // assert isTreePath([leaf], leaf, leaf);
    // assert isTreePath([child], child, child);
    // assert isTreePath([leaf,child], leaf, child);
    assert isTreePath([leaf,child,root], leaf, root);
    assert isTreePath([root,child,leaf], root, leaf);
}

predicate isValidPath(path: seq<Tree>, root: Tree) {
    forall node :: node in path ==> node in TreeSet(root)
}

lemma childInTreeSet(root: Tree, child: Tree)
    requires root != Nil && child != Nil
    requires isChild(root, child)
    ensures child in TreeSet(root)
{}

lemma validChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| > 1
    requires path[0] == start;
    requires path[|path|-1] == end;
    requires forall i :: 0 <= i < |path| ==> path[i] != Nil
    requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
    requires forall i :: 0 <= i < |path| - 1 ==> path[i+1] in TreeSet(path[i+1])
    ensures forall i :: 0 <= i < |path| - 1 ==> isValidPath(path[i..], path[i])
{
    if |path| == 2 {

    }else{
        validChildrenAlt(path[1..], path[1], end);
    }
}

lemma isDescPathAndValidImpliesAllValid(path: seq<Tree>, start: Tree, end: Tree) 
    requires isDescTreePath(path, start, end)
    requires isValidPath(path, start)
    requires |path| > 1
    ensures forall i :: 0 <= i < |path| ==> isValidPath(path[i..], path[i]);
{
    assert path[1] in TreeSet(start);
    assert isDescTreePath(path[1..], path[1], end);
    assert isValidPath(path[1..], start);
    DescTreePathNotNil(path, start, end);
    DescPathChildren(path, start, end);
    assert forall i :: 0 <= i < |path| ==> path[i] in path;
    validChildrenAlt(path, start, end);
}

lemma DescPathIsAscPath(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| >= 1
    requires isDescTreePath(path, start, end)
    ensures isAscTreePath(reverse(path), end, start)
{
    DescTreePathNotNil(path, start, end);
    ReverseIndexAll(path);
    if |path| == 1 {} else {
        DescPathChildrenReverse(path, start, end);
        AscPathChildrenAlt(reverse(path), end, start);
    }
}
lemma AscTreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| >= 1
    requires isAscTreePath(path, start, end)
    ensures forall node :: node in path ==> node != Nil
{
    if |path| == 1 {
    }else if |path| > 1 {
        assert path == [path[0]]+path[1..];
        AscTreePathNotNil(path[1..], path[1], end);
    }
}

lemma AscPathChildrenReverse(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| > 1
    requires isAscTreePath(path, start, end)
    ensures forall i :: 0 <= i < |reverse(path)| - 1 ==> isChild(reverse(path)[i], reverse(path)[i+1])
{
    AscPathChildren(path, start, end);
    ReverseIndexAll(path);
}

lemma AscPathIsDescPath(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| >= 1
    requires isAscTreePath(path, start, end)
    ensures isDescTreePath(reverse(path), end, start)
{
    AscTreePathNotNil(path, start, end);
    ReverseIndexAll(path);
    // reversePreservesMultiset(path);
    if |path| == 1 {

    }else{
        // assert path[0] == start;
        // assert path[ |path| - 1] == end;
        // assert reverse(path)[0] == end;
        // assert reverse(path)[|path|-1] == start;
        AscPathChildrenReverse(path, start, end);
        // assert forall x :: x in reverse(path) ==> x in path && x != Nil;
        assert forall i :: 0 <= i < |reverse(path)| ==> reverse(path)[i] in path && reverse(path)[i] != Nil;
        DescPathChildrenAlt(reverse(path), end, start);
    }
}
lemma DescPathPlusDescPath(path: seq<Tree>, start: Tree, middle: Tree, pathtwo: seq<Tree>, end: Tree)
    requires start != Nil
    requires end != Nil
    requires middle != Nil
    requires isDescTreePath(path, start, middle)
    requires isDescTreePath(pathtwo, middle, end)
    requires |path| > 1
    requires |pathtwo| > 1
    ensures isDescTreePath(path + pathtwo[1..], start, end)
    ensures |path + pathtwo[1..]| == |path|+|pathtwo|-1;
{
    DescPathChildren(path, start, middle);
    DescPathChildren(pathtwo, middle, end);
    DescTreePathNotNil(path, start, middle);
    DescTreePathNotNil(pathtwo, middle, end);
    assert forall i :: 0 <= i < |path| ==> path[i] in path;
    assert forall i :: 0 <= i < |pathtwo| ==> pathtwo[i] in pathtwo;
    DescPathChildrenAlt(path + pathtwo[1..], start, end);
}

lemma {:verify false} DescTreePathToTreeHeight(root: Tree, h: int, end: Tree, path: seq<Tree>) 
    requires root != Nil
    requires h >=0
    requires (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root))  && isDescTreePath(path, root, end) && |path| == h+1 && isValidPath(path, root) && distinct(path)
    ensures h == TreeHeight(root)
{
    if root.left == Nil && root.right == Nil {

    }else if root.left != Nil && root.right == Nil {
        isDescPathAndValidImpliesAllValid(path, root, end);
        assert isValidPath(path[1..], path[1]);
        assert distinct(path[1..]);
        assert isDescTreePath(path[1..], path[1], end);
        assert |path[1..]| == h;
        DescTreePathToTreeHeight(path[1],h-1, end, path[1..]);
    } else if root.left == Nil && root.right != Nil {
        isDescPathAndValidImpliesAllValid(path, root, end);
        assert isValidPath(path[1..], path[1]);
        assert distinct(path[1..]);
        assert isDescTreePath(path[1..], path[1], end);
        assert |path[1..]| == h;
        DescTreePathToTreeHeight(path[1],h-1, end, path[1..]);
    }else{
        isDescPathAndValidImpliesAllValid(path, root, end);
        assert isValidPath(path[1..], path[1]);
        assert distinct(path[1..]);
        assert isDescTreePath(path[1..], path[1], end);
        assert |path[1..]| == h;
        DescTreePathToTreeHeight(path[1],h-1, end, path[1..]);
        assert isChild(root, path[1]);
        assert TreeHeight(path[1]) == h - 1;
        assert TreeHeight(root) == h;

    }
}


lemma {:verify } TreeHeightToDescTreePath(root: Tree, h: int) 
    requires root != Nil
    requires h == TreeHeight(root)
    ensures exists end: Tree, path: seq<Tree> :: (isLeaf(end) && end in TreeSet(root))  && isDescTreePath(path, root, end) && |path| == h+1 && isValidPath(path, root) && distinct(path)
{
    if h == 0 {
        assert isDescTreePath([root], root, root);
        assert isValidPath([root], root);
        assert distinct([root]);
        assert root in TreeSet(root);
    }else if h >= 1 {
        if root.left != Nil && TreeHeight(root.left) == h-1 {
            TreeHeightToDescTreePath(root.left, h-1);
            TreeSetChildInTreeSet(root, root.left);
            var end: Tree, path: seq<Tree> :| isLeaf(end) && end in TreeSet(root.left) && isDescTreePath(path, root.left, end) && |path| == h && isValidPath(path, root.left) && distinct(path);
            assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
            parentNotInTreeSet(root, root.left);
            distincts([root], path);
            assert distinct([root]+path);
            assert isValidPath([root]+path, root);
        } else if root.right != Nil && TreeHeight(root.right) == h-1 {
            TreeHeightToDescTreePath(root.right, h-1);
            TreeSetChildInTreeSet(root, root.right);
            var end: Tree, path: seq<Tree> :| isLeaf(end) && end in TreeSet(root.right) && isDescTreePath(path, root.right, end) && |path| == h && isValidPath(path, root.right) && distinct(path);
            assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
            parentNotInTreeSet(root, root.right);
            distincts([root], path);
            assert distinct([root]+path);
            assert isValidPath([root]+path, root);
        }
    }
}

lemma S(path: seq<Tree>, start: Tree, end: Tree)
    requires |path| > 1
    requires start != Nil && end != Nil
    requires isDescTreePath(path, start, end)
    requires isValidPath(path, start);
    requires ChildrenAreSeparate(start)
    ensures end in TreeSet(start.left) ==> path[1] == start.left
    ensures end in TreeSet(start.right) ==> path[1] == start.right
{
    // DescPathChildren(path, start, end);
    isDescPathAndValidImpliesAllValid(path, start, end);
    // if end in TreeSet(start.left) {
    //     assert end !in TreeSet(start.right);
    //     assert isChild(start, start.left);
    //     assert isChild(path[0], path[1]);
    // } else if end in TreeSet(start.right) {
    //     assert end !in TreeSet(start.left);
    //     assert isChild(start, start.left);
    //     assert isChild(path[0], path[1]);
    // }
}

ghost predicate isPath(path: seq<Tree>, start: Tree, end: Tree, root: Tree) {
    isTreePath(path,start, end) && isValidPath(path, root) && distinct(path)
}

lemma isPathSlices(path: seq<Tree>, start: Tree, end: Tree, root: Tree) 
    requires |path| >= 1
    requires isPath(path, start, end, root)
    ensures forall i :: 0 < i < |path| ==> isPath(path[..(i+1)], start, path[i], root) && isPath(path[i..], path[i], end, root)
{
    TreePathNotNil(path, start, end);
    TreePathsAreTheSameAlt(path, start, end);
    forall i | 0 < i < |path| 
        ensures isPath(path[..(i+1)], start, path[i], root) && isPath(path[i..], path[i], end, root)
    {
        assert path == path[..i]+path[i..];
        TreePathChildrenAlt(path[..(i+1)], start, path[i]);
        TreePathChildrenAlt(path[i..], path[i], end);
        assert isValidPath(path[..i], root);
        assert isValidPath(path[i..], root);
        assert distinct(path[..i]);
        assert distinct(path[i..]);
    }
}

ghost predicate isDiameter(path: seq<Tree>, start: Tree, end: Tree, root: Tree) {
    isPath(path, start, end, root) && forall paths: seq<Tree>, pathStart: Tree, pathEnd: Tree :: isPath(paths, pathStart, pathEnd, root) ==> |path| >= |paths|
}

ghost function tallestChild(root: Tree): Tree {
    if root == Nil then Nil else if root != Nil && TreeHeight(root.left) > TreeHeight(root.right) then root.left else root.right
}

lemma RightBounded(root: Tree, h: int) 
    requires root != Nil && root.right != Nil
    requires TreeHeight(root) == h
    ensures TreeHeight(root.right) <= h-1
    ensures TreeHeight(root.left) <= h-1
{

}

lemma RootBounded(root: Tree, h: int) 
    requires root != Nil
    requires TreeHeight(root) == h
    ensures (TreeHeight(root.right) == h-1 && TreeHeight(root.left) <= h-1) || (TreeHeight(root.right) <= h-1 && TreeHeight(root.left) == h-1)
{

}

predicate isLeaf(node: Tree ) {
    node != Nil && node.right == Nil && node.left == Nil
}

lemma notRootNotDesc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires isValidPath(path, root)
    requires root in path
    ensures start != root ==> !isDescTreePath(path, start, end)
{
    if isDescTreePath(path, start, end) {
        descRoot(root, start, end, path);
    }
}

lemma descRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>) 
    requires isDescTreePath(path, start, end)
    requires isValidPath(path, root)
    requires root in path
    ensures start == root
{
    if start == root {

    }else {
        assert path[0] != root;
        assert path == [path[0]]+path[1..];
        assert root in path[1..];
        DescPathChildren(path, start, end);
        var i :| 0 < i< |path| && path[i] == root;
        assert isChild(path[i-1], root);
        parentNotInTreeSet(path[i-1], root);
        assert false;
    }
}

lemma LastNotRootNotAsc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires isValidPath(path, root)
    requires root in path
    ensures end != root ==> !isAscTreePath(path, start, end)
{
    if isAscTreePath(path, start, end) {
        ascRoot(root, start, end, path);
    }
}

lemma ascRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires isAscTreePath(path, start, end)
    requires isValidPath(path, root)
    requires root in path
    ensures end == root
{
    if end == root {

    }else {
        assert path[|path|-1] != root;
        AscPathChildren(path,start,end);
        var i :| 0 <= i < |path|-1 && path[i] == root;
        assert isChild(path[i+1], path[i]);
        parentNotInTreeSet(path[i+1], root);
        assert false;
    }
}

lemma parentsAreTheSame(p1: Tree, p2: Tree, child: Tree)
    requires p1 != Nil && p2 != Nil && child != Nil
    requires isChild(p1, child)
    requires isChild(p2, child)
    ensures p1 == p2

lemma pathStartingAtRootDescSlice(root: Tree, start: Tree, end: Tree, path: seq<Tree>, i: int)
    requires root != Nil
    requires root in path && path[0] == root
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires 0 < i <= |path|
    requires isDescTreePath(path[0..i], root, path[i-1])
    requires |path| >= 1
    decreases |path| - i
    ensures isDescTreePath(path, root, end)
{
    TreePathNotNil(path, start, end);
    TreePathsAreTheSameAlt(path, start,end);
    if i < |path| {
        if isChild(path[i-1], path[i]) {
            if i == 1 {
                assert isDescTreePath(path[0..1], root, path[i-1]);
            }else{

                DescPathChildren(path[0..i], root, path[i-1]);
            }
            DescPathChildrenAlt(path[0..(i+1)], root, path[i]);
            assert isDescTreePath(path[0..(i+1)], root, path[i]);
            pathStartingAtRootDescSlice(root, start, end, path, i+1);
        }else if isChild(path[i], path[i-1]) {
            if i == 1 {
                parentNotInTreeSet(path[i],root);
            }else{
                DescPathChildren(path[0..i], root, path[i-1]);
                assert isChild(path[i-2],path[i-1]);
                parentsAreTheSame(path[i-2], path[i], path[i-1]);
                assert path[i-2] == path[i];
                assert false;
            }
            assert false;
        }else{
            assert !isParentOrChild(path[i-1], path[i]);
            assert false;
        }
    }else{
        assert i == |path|;
        assert isDescTreePath(path[0..|path|], root, path[|path|-1]);
        assert path[0..|path|] == path;
    }
}

lemma pathStartingAtRootDesc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path && path[0] == root
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires |path| >= 1
    decreases |path|
    ensures isDescTreePath(path, root, end)
{
    if |path| == 1 {

    }else{
        if isChild(path[1], root) {
            parentNotInTreeSet(path[1], root);
            assert false;
        }else if isChild(root, path[1]) {
            assert path[1] == root.left || path[1] == root.right;
            assert isDescTreePath([root, path[1]], root, path[1]);
            pathStartingAtRootDescSlice(root, start, end, path, 1);
        }
    }
}

lemma pathEndingAtRootAsc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path && path[|path|-1] == root
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires |path| >= 1
    decreases |path|
    ensures isAscTreePath(path, root, end)
// by a similar argument to pathStartingAtRootDesc

lemma pathOptions(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    decreases |path|
    ensures isAscTreePath(path, start, end) || isDescTreePath(path, start, end) || exists i :: 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end)
{
    if isAscTreePath(path, start, end) {

    } else if isDescTreePath(path, start, end) {

    }else{
        assert !isAscTreePath(path, start, end);
        assert !isDescTreePath(path, start, end);
        if path[0] == root {
            if |path| == 1 {
                assert exists i :: 0 <= i < |path| && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
            }else{
                assert isAscTreePath(path[..(0+1)], start, root);
                // assert isDescTreePath(path[0..], root, end);
                // assert exists i :: 0 <= i < |path| && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
                pathStartingAtRootDesc(root, start, end, path);
                assert false;
            }
        }else if path[|path|-1] == root {
            pathEndingAtRootAsc(root,start, end, path);
            assert false;
        }else{
            assert root in path[1..];
            isPathSlices(path, start, end, root);
            var i :| 0 < i < |path|-1 && path[i] == root;
            // assert path == path[..(i+1)]+path[i+1..];
            assert path[..i+1][|path[..i+1]|-1] == root;
            assert path[i..][0] == root;
            assert isPath(path[..(i+1)], start, path[i], root);
            assert isPath(path[i..], root, end, root);
            pathStartingAtRootDesc(root, path[i], end, path[i..]);
            pathEndingAtRootAsc(root, start, path[i], path[..(i+1)]);
        }
    }
}

lemma rootPathAtMost3h(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    ensures |path| <= 2 * h + 1
{
    assert start in TreeSet(root);
    assert end in TreeSet(root);
    RootBounded(root, h);
    pathOptions(root, start,end, path);

    if isDescTreePath(path, start, end) {
        descRoot(root, start, end, path);
        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |path| <= |maxpath|;
    } else if isAscTreePath(path, start, end) {
        ascRoot(root, start, end, path);
        assert end == root;
        AscPathIsDescPath(path, start, root);
        ReverseIndexAll(path);
        assert |reverse(path)| == |path|;
        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |path| <= |maxpath|;
    } else if i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end) {
        ReverseIndexAll(path[..(i+1)]);
        AscPathIsDescPath(path[..(i+1)],start, root);

        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |(path[..(i+1)])| <= h+1;
        assert |path[i..]| <= h+1;
        assert |path| == |reverse(path[..(i+1)])| + |path[i+1..]|;
        assert |path| <= h+1 + h;
    }
}

lemma {:verify false} {:induction false} DiameterAtMost3h(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isDiameter(path, start, end, root)
    ensures |path|  <= 2*h+1
{
    assert start in TreeSet(root);
    assert end in TreeSet(root);
    RootBounded(root, h);
    if isLeaf(root) {
        assert h == 0;
        assert start == end == root;
        assert |path| == 1;
    }else if root.right == Nil && isLeaf(root.left) {
        assert h == 1;
        if |path| > 2 {
            pigeonHoles(TreeSet(root),path, 2);
            assert false;
        }
        assert |path|  <= 2*h+1;
    }else if root.left == Nil && isLeaf(root.right) {
        assert h == 1;

        if |path| > 2 {
            pigeonHoles(TreeSet(root),path, 2);
            assert false;
        }
        assert |path|  <= 3;
    }else if isLeaf(root.left) && isLeaf(root.right) {
        assert h == 1;
        if |path| > 3 {
            pigeonHoles(TreeSet(root),path, 3);
            assert false;
        }
        assert |path|  <= 2*h+1;
    }else if root.left != Nil && root.right != Nil {
        assert root.right != Nil;
        assert root.left != Nil;
        if TreeHeight(root.right) == h-1 && TreeHeight(root.left) <= h-1 {
            var lh :| lh == TreeHeight(root.left);
            assert lh <= h-1;
            TreeHeightToDescTreePath(root.left, lh);
            ghost var lpath: seq<Tree>, lend: Tree :| (isLeaf(lend) && lend in TreeSet(root.left))  && isDescTreePath(lpath, root.left, lend) && |lpath| == lh+1 && isValidPath(lpath, root.left) && distinct(lpath);
            TreeHeightToDescTreePath(root.right, h-1);
            ghost var rpath: seq<Tree>, rend: Tree :| (isLeaf(rend) && rend in TreeSet(root.right))  && isDescTreePath(rpath, root.right, rend) && |rpath| == h && isValidPath(rpath, root.right) && distinct(rpath);

            assert |path|  <= 2*h+1;
        } else if TreeHeight(root.right) <= h-1 && TreeHeight(root.left) == h-1 {

            assert |path|  <= 2*h+1;
        }
    }
}

lemma {:verify false} DiameterIncludesRootOrInDeepestTree(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires isDiameter(path, start, end, root)
    ensures root in path || (root !in path && isValidPath(path, tallestChild(root)))
{
    if root in path {

    }else{

    }
}

lemma childHeightIsLessThanPath(root: Tree, child:Tree, h: int, end: Tree)
    requires root != Nil
    requires ChildrenAreSeparate(root)
    requires h == TreeHeight(root)
    requires isChild(root, child)
    requires TreeHeight(child) <= h-1
    ensures forall rootedPath: seq<Tree>, anyend: Tree :: isDescTreePath(rootedPath, child, anyend)  && isValidPath(rootedPath, child) && distinct(rootedPath) ==> |rootedPath| <= h
{
    forall rootedPath: seq<Tree>, anyend: Tree | isDescTreePath(rootedPath, child, anyend)  && isValidPath(rootedPath, child) && distinct(rootedPath)
        ensures |rootedPath| <= h
    {
        if |rootedPath| <= h {

        }else if |rootedPath| > h {
            TreeHeightMax(child);
            S(rootedPath, child, anyend);
            if anyend in TreeSet(child.left) {
                if child.left == Nil {
                    assert false;
                }else{
                    childHeightIsLessThanPath(child, child.left, TreeHeight(child), anyend);
                    assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, child.left, anyend)  && isValidPath(childPaths, child.left) && distinct(childPaths) ==> |childPaths| <= TreeHeight(child);
                    assert rootedPath[1] == child.left;
                    assert rootedPath == [child] + rootedPath[1..];
                    isDescPathAndValidImpliesAllValid(rootedPath,child,anyend);
                    assert isDescTreePath(rootedPath[1..], child.left, anyend);
                    assert isValidPath(rootedPath[1..], child.left);
                    assert |rootedPath[1..]| <= TreeHeight(child);
                    assert false;
                }

            }else if anyend in TreeSet(child.right) {
                if child.right == Nil {
                    assert false;
                }else{

                    childHeightIsLessThanPath(child, child.right, TreeHeight(child), anyend);
                    assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, child.right, anyend)  && isValidPath(childPaths, child.right) && distinct(childPaths) ==> |childPaths| <= TreeHeight(child);
                    isDescPathAndValidImpliesAllValid(rootedPath,child,anyend);
                    assert isDescTreePath(rootedPath[1..], child.right, anyend);
                    assert false;
                }
            }else{
                assert anyend !in TreeSet(child.right) && anyend !in TreeSet(child.left);
                if anyend == child {

                }else{
                    assert anyend !in TreeSet(child);
                    assert false;
                }
            }

        }
    }
}

lemma TreeHeightToMaxDescTreePath(root: Tree, h: int, end: Tree, path: seq<Tree>) 
    requires root != Nil
    requires ChildrenAreSeparate(root)
    requires h == TreeHeight(root)
    requires end != Nil  && end in TreeSet(root)
    requires isDescTreePath(path, root, end) && |path| == h+1 && isValidPath(path, root) && distinct(path)
    ensures forall rootedPath: seq<Tree>, anyend: Tree :: isDescTreePath(rootedPath, root, anyend)  && isValidPath(rootedPath, root) && distinct(rootedPath) ==> |rootedPath| <= |path|
    
{
    TreeHeightMax(root);
    RootBounded(root, h);
    forall rootedPath: seq<Tree>, anyend: Tree | isDescTreePath(rootedPath, root, anyend)  && isValidPath(rootedPath, root) && distinct(rootedPath)
        ensures |rootedPath| <= |path|
    {
        assert rootedPath[0] == root;
        assert |rootedPath| >= 1;
        if |rootedPath| == 1 {

        }else{
            S(rootedPath, root, anyend);
            if anyend in TreeSet(root.left) {
                childHeightIsLessThanPath(root, root.left, h, anyend);
                assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, root.left, anyend)  && isValidPath(childPaths, root.left) && distinct(childPaths) ==> |childPaths| <= h;
                isDescPathAndValidImpliesAllValid(rootedPath,root,anyend);
                assert isDescTreePath(rootedPath[1..], root.left, anyend);
                assert |rootedPath[1..]| <= h;
                assert |rootedPath| <= h+1;
            }else if anyend in TreeSet(root.right) {
                childHeightIsLessThanPath(root, root.right, h, anyend);
                isDescPathAndValidImpliesAllValid(rootedPath,root,anyend);
                assert isDescTreePath(rootedPath[1..], root.right, anyend);
                assert |rootedPath[1..]| <= h;
                assert |rootedPath| <= h+1;
            }else{
                if anyend == root {

                }else{
                    assert anyend !in TreeSet(root);
                    assert false;
                }
            }
        }
    }
   
}

lemma DescTreePathNoChildren(path: seq<Tree>, root: Tree, end: Tree)
    requires root != Nil
    requires end != Nil
    requires |path| > 1
    requires isDescTreePath(path, root, end)
    ensures forall x :: x in path[1..] ==> x in TreeSet(root) - {root} 
{
    if |path| == 2 {
    }else{
        if root.left != Nil && isDescTreePath(path[1..], root.left, end) {
            parentNotInTreeSet(root,root.left);
            forall x | x in path[1..] 
                ensures x in TreeSet(root) - {root}
            {
                assert path[1..] == [path[1]]+path[2..];
            }
        }else if root.right != Nil && isDescTreePath(path[1..], root.right, end) {
            parentNotInTreeSet(root,root.right);
            forall x | x in path[1..] 
                ensures x in TreeSet(root) - {root}
            {
                assert path[1..] == [path[1]] + path[2..];
            } 
        }
    }
}

lemma DescTreePathInjective(path: seq<Tree>, root: Tree, end: Tree)
    requires root != Nil
    requires end != Nil
    requires isDescTreePath(path, root, end)
    ensures distinct(path)
{
    if |path| == 1 {

    }else{
        assert path[1] == root.left || path[1] == root.right;
        assert root != root.left && root != root.right;
        assert path == [root]+path[1..];
        var rest := path[1..];
        DescTreePathInjective(rest,path[1], end);
        assert distinct(rest);
        DescTreePathNoChildren(path, root, end);
        forall x,y | x != y && 0 <= x <= y < |path| 
            ensures path[x] != path[y]; 
        {
            if x == 0 {
                assert path[x] == root;
                assert path[y] in path[1..];
                assert path[y] != root;
            }else{
                assert path[x] != path[y];
            }
        }
    }
}

lemma DescTreePathToPath(path: seq<Tree>, root: Tree, end: Tree)
    requires root != Nil
    requires end != Nil
    requires isDescTreePath(path, root, end)
    ensures isTreePath(path, root, end)
{
    assert path[0] == root;
    assert path[|path|-1] == end;
    if |path| == 1 {
        assert path == [root];
        assert isDescTreePath([root], root, end);
        assert root == end;
        assert isTreePath([root], root, end);
    }
}

lemma AscTreePathToPath(path: seq<Tree>, root: Tree, end: Tree)
    requires root != Nil
    requires end != Nil
    requires isAscTreePath(path, root, end)
    ensures isTreePath(path, root, end)
{
    assert path[0] == root;
    assert path[|path|-1] == end;
    if |path| == 1 {
        assert path == [root];
        assert isAscTreePath([root], root, end);
        assert root == end;
        assert isTreePath([root], root, end);
    }
}

lemma DescTreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| >= 1
    requires isDescTreePath(path, start, end)
    ensures forall node :: node in path ==> node != Nil
    ensures forall i :: 0 <= i < |path| ==> path[i] != Nil
{
    if |path| == 1 {
    }else if |path| > 1 {
        assert path == [path[0]]+path[1..];
        DescTreePathNotNil(path[1..], path[1], end);
    }
}

lemma TreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires |path| >= 1
    requires isTreePath(path, start, end)
    ensures forall node :: node in path ==> node != Nil
    ensures forall i :: 0 <= i < |path| ==> path[i] != Nil
{
    if |path| == 1 {
    }else if |path| > 1 {
        assert path == [path[0]]+path[1..];
        TreePathNotNil(path[1..], path[1], end);
    }
}

lemma TreePlusTree(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
    requires start != Nil && root != Nil && end != Nil
    requires start != root && root != end
    requires isTreePath(path, start, root)
    requires isTreePath(pathtwo, root, end)
    ensures isTreePath(path + pathtwo[1..], start, end)
    ensures |path + pathtwo[1..]| == |path|+|pathtwo|-1
{
    TreePathsAreTheSameAlt(path, start, root);
    TreePathsAreTheSameAlt(pathtwo, root, end);
    assert isTreePathAlt(path + pathtwo[1..], start, end);
    TreePathsAreTheSame(path + pathtwo[1..], start, end);
}

lemma DescPlusAsc(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
    requires start != Nil && root != Nil && end != Nil
    requires start != root && root != end
    requires isDescTreePath(path, root, end)
    requires isAscTreePath(pathtwo, start, root)
    ensures isTreePath(pathtwo + path[1..], start, end)
{
    var result := pathtwo + path[1..];
    assert result[0] == start;
    DescTreePathToPath(path, root, end);
    AscTreePathToPath(pathtwo, start, root);
    TreePlusTree(pathtwo, start, root, path, end);
    assert |pathtwo + path[1..]| == |pathtwo| + |path| -1;
}

lemma DescPlusDesc(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
    requires start != Nil && root != Nil && end != Nil
    requires start != root && root != end
    requires isDescTreePath(path, root, end)
    requires isDescTreePath(pathtwo, root, start)
    ensures isTreePath(reverse(pathtwo) + path[1..], start, end)
{
    DescPathIsAscPath(pathtwo, root, start);
    assert isAscTreePath(reverse(pathtwo), start, root);
    DescPlusAsc(path, start, root, reverse(pathtwo), end);
}

lemma BothCases(root: Tree, left: Tree, right: Tree, h1: int, h2: int)
    requires root != Nil && left != Nil && right != Nil
    requires ChildrenAreSeparate(root)
    requires root.left == left && root.right == right
    requires TreeHeight(root.left) == h1
    requires TreeHeight(root.right) == h2
    ensures exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| == h1+h2 + 3 && isValidPath(path, root) && distinct(path);
{

        TreeHeightToDescTreePath(right, h2);
        var rpath: seq<Tree>, rend: Tree :| (isLeaf(rend) && rend in TreeSet(right))  && isDescTreePath(rpath, right, rend) && |rpath| == h2+1 && isValidPath(rpath, right) && distinct(rpath);
        assert rend in TreeSet(right);
        assert isDescTreePath([root]+rpath, root, rend);
        DescTreePathToPath(rpath, root.right, rend);
        TreeHeightToDescTreePath(left, h1);
        var lpath: seq<Tree>, lend: Tree :| (isLeaf(lend) && lend in TreeSet(left))  && isDescTreePath(lpath, left, lend) && |lpath| == h1+1 && isValidPath(lpath, left) && distinct(lpath);
        assert isDescTreePath([root]+lpath, root, lend);
        DescTreePathToPath(lpath, root.left, lend);
        
        parentNotInTreeSet(root, left);
        parentNotInTreeSet(root, right);
        assert root !in TreeSet(left);
        assert root !in TreeSet(right);
        assert lend in TreeSet(left);
        distincts([root], lpath);
        assert distinct([root]+lpath);
        reverseDistinct([root]+lpath);
        assert rend != lend;
        DescPlusDesc([root]+rpath, lend, root, [root]+lpath, rend);
        assert isTreePath(reverse([root]+lpath)+rpath, lend, rend);
        assert |[root]+lpath| == h1+2;
        ReverseIndexAll([root]+lpath);
        assert |[root]+lpath| == h1+2;
        assert |reverse([root]+lpath)+rpath| == h1+h2+3;
        distincts(reverse([root]+lpath), rpath);
}

ghost predicate largestPath(path: seq<Tree>, root: Tree) {
    forall start: Tree, end: Tree, paths: seq<Tree> :: distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) ==> |path| >= |paths|
}

ghost predicate largestPathStart(path: seq<Tree>, root: Tree) {
    forall end: Tree, paths: seq<Tree> :: distinct(paths) && isTreePath(paths, root, end)  && isValidPath(paths, root) ==> |path| >= |paths|
}

lemma lpR(root: Tree)
    requires root != Nil && root.left == Nil && root.right == Nil
    ensures largestPath([root], root)
{
    assert distinct([root]);
    assert isValidPath([root], root);
    assert isTreePath([root], root, root);

    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
     ensures |[root]| >= |paths|
    {
        if |paths| > 1 {
            assert paths[0] != paths[1];
            if isChild(paths[0], paths[1]) {
                if paths[0] == root {
                    assert false;
                }else if paths[1] == root {
                    parentNotInTreeSet(paths[0], root);
                    assert false;
                }else{
                    assert paths[0] !in TreeSet(root);
                }
            } else if isChild(paths[1], paths[0]) {
                if paths[0] == root {
                    parentNotInTreeSet(paths[1], root);
                    assert false;
                }else if paths[1] == root {
                    parentNotInTreeSet(paths[0], root);
                    assert false;
                }
            }else {
                assert false;
            }
        }else if |paths| == 0{

        }else{

        }
    }

}


// https://www.youtube.com/watch?v=2PFl93WM_ao
//Property I 
//Deepest branch contain the maximal diameter

//Suppose c1 does not contain the diameter.
//d_1 = D(c1)
//d_2 = =D(c_i)
//d1+d2+2 >= d2
//d1 = d2 + delta where delta >=0
//d1 + d2 +2 == d2+delta +d2+2 == 2*d2+delta+2 > 2*d2
//How many diameters can be in a tree with n nodes?
//Count the number of diametes in T?


lemma {:verify false} rootPlusMaxIsMax(root: Tree, lstart: Tree, lend: Tree, lpath: seq<Tree>, rstart: Tree, rend: Tree, rpath: seq<Tree>, lw: int, rw: int, rootedPath: seq<Tree>, rcStart: Tree, rcEnd: Tree) returns (maxPath: seq<Tree>)
    requires root != Nil && root.left != Nil && root.right != Nil
    requires ChildrenAreSeparate(root)
    requires isTreePath(rpath, rstart, rend) && isValidPath(rpath, root) && distinct(rpath) && largestPath(rpath, root.right)
    requires isTreePath(lpath, lstart, lend) && isValidPath(lpath, root) && distinct(lpath) && largestPath(lpath, root.left)
    requires isTreePath(rootedPath, rcStart, rcEnd) && isValidPath(rootedPath, root) && distinct(rootedPath)
    requires |rpath| == rw
    requires |lpath| == lw
    ensures largestPath(maxPath, root)
{
    if |lpath| > max(|rpath|, |rootedPath|) {
        return lpath;
    }else if |rpath| > |rootedPath| && |rpath| >= |lpath| {
        return rpath;
    }else{
        // assert largestPath(rootedPath, root);
        // return rootedPath;
    }
}

method diameter(root: Tree) returns (heightDim: (int, int))
    requires ChildrenAreSeparate(root)
    ensures root == Nil ==> heightDim == (-1, -1)
    ensures root != Nil && root.left == Nil && root.right == Nil ==> heightDim == (0, 0)
    ensures heightDim.0 == TreeHeight(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == heightDim.1  && isValidPath(path, root) && distinct(path)
{
    if root == Nil {
        return (-1, -1);
    }
    if root.left == Nil && root.right == Nil {
        ghost var path := [root];
        assert isTreePath([root], root, root);
        lpR(root);
        return (0,0);
    }
    var leftDiameter := diameter(root.left);
    var rightDiameter := diameter(root.right);
    var height := max(leftDiameter.0, rightDiameter.0) + 1;
    var dim := leftDiameter.0 + rightDiameter.0 + 2;
    var maxDiameter := max(leftDiameter.1, max(rightDiameter.1, dim));

    if root.right != Nil && root.left != Nil {
        BothCases(root, root.left, root.right, leftDiameter.0, rightDiameter.0);
        ghost var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1;
        ghost var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1;
        ghost var start, end, path :| isTreePath(path, start, end) && |path| == leftDiameter.0 + rightDiameter.0 + 3 && distinct(path);
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert maxDiameter == leftDiameter.1;
            // assert largestPath(leftPath, root.right);
        }else if rightDiameter.1 > dim {
            assert maxDiameter == rightDiameter.1;
        }else{
            assert |path| >= |rightPath|;
            assert |path| >= |leftPath|;
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            assert |path| - 1 == dim;
            assert maxDiameter == dim;
        }
    } else if root.right != Nil {
        ghost var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1 && isValidPath(rightPath, root);
        TreeHeightToDescTreePath(root.right, rightDiameter.0);
        ghost var rpath: seq<Tree>, end: Tree :| (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.right))  && isDescTreePath(rpath, root.right, end) && |rpath| == rightDiameter.0+1 && isValidPath(rpath, root.right) && distinct(rpath);
        assert isDescTreePath([root]+rpath, root, end);
        DescTreePathToPath([root]+rpath, root, end);
        assert |[root]+rpath| == rightDiameter.0+2;
        parentNotInTreeSet(root, root.right);
        assert distinct([root]+rpath);
        assert leftDiameter.0 == -1;
        assert leftDiameter.1 == -1;
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert false;
        }else if rightDiameter.1 > dim {
            assert maxDiameter == rightDiameter.1;
        }else{
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            calc {
                dim;
                leftDiameter.0 + rightDiameter.0 + 2;
                -1 + rightDiameter.0 + 2;
                rightDiameter.0 + 1;
            }
            assert maxDiameter == dim;
            assert |[root]+rpath| - 1 == dim;
        }
    } else if root.left != Nil {
        ghost var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1;
        TreeHeightToDescTreePath(root.left, leftDiameter.0);
        ghost var lpath: seq<Tree>, end: Tree :| (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.left))  && isDescTreePath(lpath, root.left, end) && |lpath| == leftDiameter.0+1 && isValidPath(lpath, root.left) && distinct(lpath);
        assert isDescTreePath([root]+lpath, root, end);
        DescTreePathToPath([root]+lpath, root, end);
        parentNotInTreeSet(root, root.left);
        assert distinct([root]+lpath);
        assert dim == leftDiameter.0 + 1;
        assert rightDiameter.0 == -1;
        assert rightDiameter.1 == -1;
        assert leftDiameter.1 >= 0;
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert maxDiameter == leftDiameter.1;
        }else if rightDiameter.1 > dim {
            assert false;
        }else{
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            assert maxDiameter == dim;
        }
    }

    return (height, maxDiameter);
}

method diameterOfBinaryTree(root: Tree) returns (maxDiameter: int)
    requires ChildrenAreSeparate(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == maxDiameter && isValidPath(path, root) && distinct(path)
{
    var result := diameter(root);
    maxDiameter := result.1;
}
}