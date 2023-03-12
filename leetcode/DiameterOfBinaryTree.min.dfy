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
import opened BinaryTree
import opened Seq

lemma notInNotEqual<A(==)>(xs: seq<A>, elem: A)
    requires elem !in xs
    ensures forall k :: 0 <= k < |xs| ==> xs[k] != elem
{

}

predicate injectiveSeq<A(==)>(s: seq<A>) {
    forall x,y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
}

lemma injectiveSeqs<A>(xs: seq<A>, ys: seq<A>)
    requires injectiveSeq(xs)
    requires injectiveSeq(ys)
    requires forall x :: x in xs ==> x !in ys 
    requires forall y :: y in ys ==> y !in xs 
    ensures injectiveSeq(xs+ys)
{
    var len := |xs + ys|;
    forall x,y | x != y && 0 <= x <= y < |xs+ys| 
        ensures (xs+ys)[x] != (xs+ys)[y] 
    {
        if 0 <= x < |xs| && 0 <= y < |xs| {
            assert (xs+ys)[x] != (xs+ys)[y];
        }else if |xs| <= x < |xs+ys| && |xs| <= y < |xs+ys| {
            assert (xs+ys)[x] != (xs+ys)[y];

        }else if 0 <= x < |xs| && |xs| <= y < |xs+ys| {
            notInNotEqual(ys, xs[x]);
            assert (xs+ys)[x] != (xs+ys)[y];
        }
    }

}

lemma reverseInjective<A>(list: seq<A>)
    requires injectiveSeq(list)
    ensures injectiveSeq(reverse(list))
{
    ReverseIndexAll(list);
}

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

lemma TreeHeightToDescTreePath(root: Tree, h: int) 
    requires root != Nil
    requires h == TreeHeight(root)
    ensures exists end: Tree, path: seq<Tree> :: (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root))  && isDescTreePath(path, root, end) && |path| == h+1 && isValidPath(path, root) && injectiveSeq(path)
{
    if h == 0 {
        assert isDescTreePath([root], root, root);
        assert isValidPath([root], root);
        assert injectiveSeq([root]);
        assert root in TreeSet(root);
    }else if h >= 1 {
        if root.left != Nil && TreeHeight(root.left) == h-1 {
            TreeHeightToDescTreePath(root.left, h-1);
            TreeSetChildInTreeSet(root, root.left);
            var end: Tree, path: seq<Tree> :| end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.left) && isDescTreePath(path, root.left, end) && |path| == h && isValidPath(path, root.left) && injectiveSeq(path);
            assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
            parentNotInTreeSet(root, root.left);
            assert injectiveSeq([root]+path);
            assert isValidPath([root]+path, root);
        } else if root.right != Nil && TreeHeight(root.right) == h-1 {
            TreeHeightToDescTreePath(root.right, h-1);
            TreeSetChildInTreeSet(root, root.right);
            var end: Tree, path: seq<Tree> :| end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.right) && isDescTreePath(path, root.right, end) && |path| == h && isValidPath(path, root.right) && injectiveSeq(path);
            assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
            parentNotInTreeSet(root, root.right);
            assert injectiveSeq([root]+path);
            assert isValidPath([root]+path, root);
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
    ensures injectiveSeq(path)
{
    if |path| == 1 {

    }else{
        assert path[1] == root.left || path[1] == root.right;
        assert root != root.left && root != root.right;
        assert path == [root]+path[1..];
        DescTreePathInjective(path[1..],path[1], end);
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
{
    if |path| == 1 {
    }else if |path| > 1 {
        assert path == [path[0]]+path[1..];
        DescTreePathNotNil(path[1..], path[1], end);
    }
}

lemma TreePlusTree(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
    requires start != Nil && root != Nil && end != Nil
    requires start != root && root != end
    requires isTreePath(path, start, root)
    requires isTreePath(pathtwo, root, end)
    ensures isTreePath(path + pathtwo[1..], start, end)
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
    ensures exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| == h1+h2 + 3 && isValidPath(path, root) && injectiveSeq(path);
{

        TreeHeightToDescTreePath(right, h2);
        var rpath: seq<Tree>, rend: Tree :| (rend != Nil && rend.left == Nil && rend.right == Nil && rend in TreeSet(right))  && isDescTreePath(rpath, right, rend) && |rpath| == h2+1 && isValidPath(rpath, right) && injectiveSeq(rpath);
        assert rend in TreeSet(right);
        assert isDescTreePath([root]+rpath, root, rend);
        DescTreePathToPath(rpath, root.right, rend);
        TreeHeightToDescTreePath(left, h1);
        var lpath: seq<Tree>, lend: Tree :| (lend != Nil && lend.left == Nil && lend.right == Nil && lend in TreeSet(left))  && isDescTreePath(lpath, left, lend) && |lpath| == h1+1 && isValidPath(lpath, left) && injectiveSeq(lpath);
        assert isDescTreePath([root]+lpath, root, lend);
        DescTreePathToPath(lpath, root.left, lend);
        
        parentNotInTreeSet(root, left);
        parentNotInTreeSet(root, right);
        assert root !in TreeSet(left);
        assert root !in TreeSet(right);
        assert lend in TreeSet(left);
        assert injectiveSeq([root]+lpath);
        reverseInjective([root]+lpath);
        assert rend != lend;
        DescPlusDesc([root]+rpath, lend, root, [root]+lpath, rend);
        assert isTreePath(reverse([root]+lpath)+rpath, lend, rend);
        assert |[root]+lpath| == h1+2;
        ReverseIndexAll([root]+lpath);
        assert |[root]+lpath| == h1+2;
        assert |reverse([root]+lpath)+rpath| == h1+h2+3;
        injectiveSeqs(reverse([root]+lpath), rpath);
}

ghost predicate largestPath(path: seq<Tree>, root: Tree) {
    forall start: Tree, end: Tree, paths: seq<Tree> :: injectiveSeq(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) ==> |path| >= |paths|
}

method diameter(root: Tree) returns (heightDim: (int, int))
    requires ChildrenAreSeparate(root)
    ensures root == Nil ==> heightDim == (-1, -1)
    ensures root != Nil && root.left == Nil && root.right == Nil ==> heightDim == (0, 0)
    ensures heightDim.0 == TreeHeight(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == heightDim.1  && isValidPath(path, root) && injectiveSeq(path)
{
    if root == Nil {
        return (-1, -1);
    }
    if root.left == Nil && root.right == Nil {
        ghost var path := [root];
        assert isTreePath([root], root, root);
        return (0,0);
    }
    var leftDiameter := diameter(root.left);
    var rightDiameter := diameter(root.right);
    var height := max(leftDiameter.0, rightDiameter.0) + 1;
    var dim := leftDiameter.0 + rightDiameter.0 + 2;
    var maxDiameter := max(leftDiameter.1, max(rightDiameter.1, dim));

    if root.right != Nil && root.left != Nil {
        BothCases(root, root.left, root.right, leftDiameter.0, rightDiameter.0);
        var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1;
        var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1;
        var start, end, path :| isTreePath(path, start, end) && |path| == leftDiameter.0 + rightDiameter.0 + 3 && injectiveSeq(path);
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert maxDiameter == leftDiameter.1;
        }else if rightDiameter.1 > dim {
            assert maxDiameter == rightDiameter.1;
        }else{
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            assert |path| - 1 == dim;
            assert maxDiameter == dim;
        }
    } else if root.right != Nil {
        var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1 && isValidPath(rightPath, root);
        TreeHeightToDescTreePath(root.right, rightDiameter.0);
        var rpath: seq<Tree>, end: Tree :| (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.right))  && isDescTreePath(rpath, root.right, end) && |rpath| == rightDiameter.0+1 && isValidPath(rpath, root.right) && injectiveSeq(rpath);
        assert isDescTreePath([root]+rpath, root, end);
        DescTreePathToPath([root]+rpath, root, end);
        assert |[root]+rpath| == rightDiameter.0+2;
        parentNotInTreeSet(root, root.right);
        assert injectiveSeq([root]+rpath);
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
        var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1;
        TreeHeightToDescTreePath(root.left, leftDiameter.0);
        var lpath: seq<Tree>, end: Tree :| (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.left))  && isDescTreePath(lpath, root.left, end) && |lpath| == leftDiameter.0+1 && isValidPath(lpath, root.left) && injectiveSeq(lpath);
        assert isDescTreePath([root]+lpath, root, end);
        DescTreePathToPath([root]+lpath, root, end);
        parentNotInTreeSet(root, root.left);
        assert injectiveSeq([root]+lpath);
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
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == maxDiameter && isValidPath(path, root) && injectiveSeq(path)
{
    var result := diameter(root);
    maxDiameter := result.1;
}