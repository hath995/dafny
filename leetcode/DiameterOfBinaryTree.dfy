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
// include "../lib/seq.dfy"
include "../lib/binaryTree.dfy"
import opened BinaryTree
// import opened Seq
function reverse<A(==)>(x: seq<A>): seq<A> 

{
    if x == [] then [] else reverse(x[1..])+[x[0]]
}

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

predicate isPath(paths: seq<Tree>) {
    if |paths| == 0 then false else if |paths| == 1 then match paths[0] {
        case Nil => false
        case Node(val, left, right) => true
    } else match paths[0] {
        case Nil => false
        case Node(val, left, right) => (left == paths[1] || right == paths[1] || (paths[1] != Nil && (paths[0] == paths[1].left || paths[0] == paths[1].right))) && isPath(paths[1..])
    }
}

predicate isValidTreePath(path: seq<Tree>, start: Tree, end: Tree) {
    isTreePath(path, start, end) && exists root: Tree :: root != Nil && root in path && (forall node: Tree :: (node in path) ==> node in TreeSet(root))
}

predicate isTreePath(path: seq<Tree>, start: Tree, end: Tree) {
    if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else match path[0] {
        case Nil => false
        case Node(val, left, right) => path[0] == start && (left == path[1] || right == path[1] || (path[1] != Nil && (path[0] == path[1].left || path[0] == path[1].right))) && isTreePath(path[1..], path[1], end)
    }
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

predicate isAscTreePath(paths: seq<Tree>, start: Tree, end: Tree) {
    if |paths| == 0 then false else if |paths| == 1 then match paths[0] {
        case Nil => false
        case Node(val, left, right) => start == paths[0] && end == start
    } else match paths[0] {
        case Nil => false
        case Node(val, left, right) => end != Nil && paths[|paths|-1] == end && start == paths[0] && paths[1] != Nil  && ((paths[0] == paths[1].left && isAscTreePath(paths[1..], paths[1], end)) || (paths[0] == paths[1].right && isAscTreePath(paths[1..], paths[1], end)))
    }
}


predicate isAscPath(paths: seq<Tree>, root: Tree) {
    if |paths| == 0 then false else if |paths| == 1 then match paths[0] {
        case Nil => false
        case Node(val, left, right) => root == paths[0]
    } else match paths[0] {
        case Nil => false
        case Node(val, left, right) => root == paths[0] && paths[1] != Nil && isAscPath(paths[1..], paths[1]) && (paths[0] == paths[1].left  || paths[0] == paths[1].right)
    }
}

predicate isDescPath(paths: seq<Tree>, root: Tree) {
    if |paths| == 0 then false else if |paths| == 1 then match paths[0] {
        case Nil => false
        case Node(val, left, right) => paths[0] == root
    } else match paths[0] {
        case Nil => false
        case Node(val, left, right) => paths[0] == root && ((left == paths[1] && isDescPath(paths[1..], left)) || (right == paths[1] && isDescPath(paths[1..], right)))
    }
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
// assert root !in TreeSet(root.left);
// assert root !in TreeSet(root.right);
// assert parent !in {root};
// assert parent in TreeSet(root.left)+TreeSet(root.right);

lemma {:verify false} isPathKinds(paths: seq<Tree>, root: Tree)
    requires validPath(paths, root)
    ensures isDescPath(paths, root) || isAscPath(paths, root) || exists k: nat :: k < |paths| && paths == paths[0..k] + paths[k..] && isAscPath(paths[0..k], root) && isDescPath(paths[k..], root)
{
    assert |paths| > 0;
    if |paths| == 1 {

    } else if paths[0] == root {
        if isDescPath(paths, root) {

        }else{
            assert !((root.left == paths[1] && isDescPath(paths[1..], root.left)) || (root.right == paths[1] && isDescPath(paths[1..], root.right)));
            assert !(root.left == paths[1] && isDescPath(paths[1..], root.left)) && !(root.right == paths[1] && isDescPath(paths[1..], root.right));
            assert (root.left != paths[1] || !isDescPath(paths[1..], root.left)) && (root.right != paths[1] || !isDescPath(paths[1..], root.right));
            if root.left != paths[1] || !isDescPath(paths[1..], root.left) {
                if root.left != paths[1] && isDescPath(paths[1..], root.left) {
                    assert false;
                } else if root.left == paths[1] && !isDescPath(paths[1..], root.left) {
                    
                }

            } else if root.right != paths[1] || !isDescPath(paths[1..], root.right) {

                if root.right != paths[1] && isDescPath(paths[1..], root.right) {

                } else if root.right == paths[1] && !isDescPath(paths[1..], root.right) {

                }
            }
            assert false;
        }
    } else if paths[|paths|-1] == root {

    }else{

    }
}


method TestPath() {
    var rootleaf := Node(4, Nil, Nil);
    var leaf := Node(3, Nil, Nil);
    var child := Node(2, Nil, leaf);
    var root := Node(1, child, rootleaf);
    assert isPath([leaf, child, root]);
    // assert isPath([leaf, child, root, rootleaf]);
    assert !isTreePath([root, rootleaf], leaf, rootleaf);
    assert isTreePath([leaf, child, root], leaf, root);
    assert isTreePath([root, rootleaf], root, rootleaf);
    assert isTreePath([leaf, child, root, rootleaf], leaf, rootleaf);
    assert isPath([root, child, leaf]);
    assert isDescPath([root, child, leaf], root);
    assert isDescTreePath([root, child, leaf], root, leaf);
    assert !isDescTreePath([root], root, leaf);
    assert isDescTreePath([root, rootleaf],root, rootleaf);
    assert isPath([root, child]);
    assert isPath([child, leaf]);
    assert isPath([leaf, child]);
    // assert isTreePath([leaf], leaf, leaf);
    // assert isTreePath([child], child, child);
    // assert isTreePath([leaf,child], leaf, child);
    assert isTreePath([leaf,child,root], leaf, root);
    assert isTreePath([root,child,leaf], root, leaf);
}

predicate validPath(path: seq<Tree>, root: Tree) {
    isPath(path) && forall node :: node in path ==> node in TreeSet(root) && root in path
}

lemma {:verify false} AscPathIsDescPath(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires |path| >= 1
    requires isAscTreePath(path, start, end)
    ensures isDescTreePath(reverse(path), end, start)
{
    assert path[0] == start;
    assert path[ |path| - 1] == end;
}

lemma {:verify false} TreeHeightToDescPath(root: Tree, h: int)
    requires root != Nil
    requires h == TreeHeight(root)
    ensures exists path: seq<Tree> :: isDescPath(path, root)
{
    if h == 0 {
        assert isDescPath([root], root);
    }else if h > 0 {

    }
}

lemma  TreeHeightLeaf(root: Tree)
    requires root != Nil
    requires TreeHeight(root) == 0
    ensures root.left == Nil && root.right == Nil
{}

lemma TreeHeightToDescTreePath(root: Tree, h: int) 
    requires root != Nil
    requires h == TreeHeight(root)
    ensures exists end: Tree, path: seq<Tree> :: (end != Nil && end.left == Nil && end.right == Nil)  && isDescTreePath(path, root, end) && |path| == h+1
{
    if h == 0 {
        assert isDescTreePath([root], root, root);
    }else if h >= 1 {
        if root.left != Nil && TreeHeight(root.left) == h-1 {
            TreeHeightToDescTreePath(root.left, h-1);
            var end: Tree, path: seq<Tree> :| end != Nil && end.left == Nil && end.right == Nil && isDescTreePath(path, root.left, end) && |path| == h;
            assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
        } else if root.right != Nil && TreeHeight(root.right) == h-1 {
            TreeHeightToDescTreePath(root.right, h-1);
            var end: Tree, path: seq<Tree> :| end != Nil && end.left == Nil && end.right == Nil && isDescTreePath(path, root.right, end) && |path| == h;
            assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
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
// assert path[2] != Nil;
// assert root.left in TreeSet(root);
// assert root !in TreeSet(root.left);
// assert root.left in TreeSet(root) - {root};
// DescTreePathNoChildren(path[2..], root.left, end); //required if induction false

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
        // assert forall x :: x in path[1..] ==> x != root;
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

lemma DescTreePathSets(path: seq<Tree>, root: Tree, end: Tree)
    requires root != Nil
    requires end != Nil
    requires isDescTreePath(path, root, end)
    ensures forall node :: node in path ==> node in TreeSet(root)
{}

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

lemma AscTreePathSlices(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires isAscTreePath(path, start, end)
    ensures forall k :: 0 <= k < |path| ==> isAscTreePath(path[k..], path[k], end);
{

}

lemma {:verify false} AscTreePathSlicesBack(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires isAscTreePath(path, start, end)
    ensures forall k :: 0 < k < |path| ==> isAscTreePath(path[..k], start, path[k-1]);
{
    AscTreePathNotNil(path, start, end);
    forall k | 0 < k < |path| 
        ensures isAscTreePath(path[..k], start, path[k-1])
    {
        if k == 1 {

        }else if k > 1{
            var test := path[..k];
            assert test[|test|-1] == path[k-1];
            assert path[k-1] in path;
            assert path[k-1] != Nil;
            assert path[k-2] in path;
            assert path[k-2] != Nil;
            assert test[0] == start;
            assert k-2 >= 0;
            AscTreePathSlicesBack(path[..(k-1)], start, path[k-2]);
        }
    }
}

lemma {:verify false} {:induction false} AscTreePathSets(path: seq<Tree>, start: Tree, end: Tree)
    requires start != Nil
    requires end != Nil
    requires isAscTreePath(path, start, end)
    ensures forall node :: node in path ==> node in TreeSet(end)
{
    AscTreePathNotNil(path, start, end);
    if |path| == 1 {

    }else if |path| > 1 {
        assert path[|path|-1] == end;
        assert |path|-2 >= 0;
        assert path[|path|-2] in path;
        assert path[|path|-2] != Nil;
        // assert isAscPath(paths[|])
        assert path == path[0..|path|-2]+path[|path|-2..];
        calc {
            path[|path|-2..];
            [path[|path|-2]]+path[|path|-1..];
            [path[|path|-2]]+[path[ |path|-1]]+path[ |path|..];
            [path[|path|-2]]+[path[ |path|-1]]+[];
            [path[|path|-2] , path[ |path|-1]];
        }
        // assert path == path[0..|path|-2]+[path[|path|-2], path[|path|-1]];
        AscTreePathSlices(path, start, end);
        assert isAscTreePath(path[|path|-2..], path[|path|-2], end);
        assert path[|path|-2..][1] == end;
        // assert |path[|path|-2..]| == 2;
        assert path[|path|-2] == end.right || path[|path|-2] == end.left;
        assert isAscTreePath(path[..|path|-1], start, path[|path|-2]);
    }
}




lemma {:induction false} ValidDescTreePathToPath(path: seq<Tree>, root: Tree, end: Tree)
    requires root != Nil
    requires end != Nil
    requires isDescTreePath(path, root, end)
    ensures isValidTreePath(path, root, end)
{
    if |path| == 1 {
        assert path == [root];
        assert isDescTreePath([root], root, end);
        assert root in TreeSet(root);
        assert root == end;
        assert isTreePath([root], root, end);
    }else if |path| > 1 {
        assert path[0] == root;
        assert root in path;
        assert path[1] != Nil;
        if path[1] == root.left {
            ValidDescTreePathToPath(path[1..], root.left, end);
            // TreeSetChildInTreeSet(root, root.left);
            // assert isValidTreePath(path[1..], root.left, end);
            DescTreePathSets(path[1..], root.left, end);
            
        } else if path[1] == root.right {
            ValidDescTreePathToPath(path[1..], root.right, end);
            // TreeSetChildInTreeSet(root, root.right);
            DescTreePathSets(path[1..], root.right, end);

        }
    }
}

lemma DescPathToPath(path: seq<Tree>, root: Tree)
    requires root != Nil
    requires isDescPath(path, root)
    ensures validPath(path, root)
{
    if |path| == 1 {
        assert path == [root];
        var ts := TreeSet(root);
        assert forall x :: x in path ==> x in ts;
        assert validPath([root], root);
    }else if |path| > 1 {
        assert path == [root]+path[1..];
        assert path[1] != Nil;
    }
}

lemma {:verify }  TreeHeightToTreePath(root: Tree, h: int)
    requires root != Nil
    requires h == TreeHeight(root)
    ensures exists path: seq<Tree>, end: Tree :: isTreePath(path, root, end)// && |path| == h - 1
{
    TreeHeightToDescTreePath(root, h);
    var end: Tree, path: seq<Tree> :| end != Nil && isDescTreePath(path, root, end);
    DescTreePathToPath(path, root, end);
}

lemma Situation(path: seq<Tree>, root: Tree)
    requires root != Nil
    requires isDescPath(path, root.left)
    ensures isDescPath([root]+path, root)
    ensures isPath([root]+path)
    ensures exists apath: seq<Tree> :: isPath(apath) && validPath(apath, root)
{
    DescPathToPath(path, root.left);
    assert isPath(path);
    var test := [root]+path;
    assert isPath([root]+ path);
}

lemma SituationR(path: seq<Tree>, root: Tree)
    requires root != Nil
    requires isDescPath(path, root.right)
    ensures isDescPath([root]+path, root)
    ensures isPath([root]+path)
    ensures exists apath: seq<Tree> :: isPath(apath) && validPath(apath, root)
{
    DescPathToPath(path, root.right);
    assert isPath(path);
    var test := [root]+path;
    assert isPath([root]+ path);
}

lemma {:verify false} {:induction false} TreeHeightToPath(root: Tree, h: int)
    requires root != Nil
    requires h == TreeHeight(root)
    ensures exists path: seq<Tree> :: validPath(path, root)// && |path| == h - 1
{
    if root.left == Nil && root.right == Nil {
        assert h >= 0;
        assert validPath([root], root);
        assert TreeHeight(root) == 0;
        assert exists path: seq<Tree> :: validPath(path, root);
    }else if h > 0 {
        assert h == max(TreeHeight(root.left), TreeHeight(root.right)) + 1;

        assert h - 1 >= 0;
        if TreeHeight(root.left) > TreeHeight(root.right) && TreeHeight(root.left) == h - 1 {
            assert root.left != Nil;
            TreeHeightToDescPath(root.left, h-1);
            // var leftpath:seq<Tree> :| isValidPath(leftpath, root.left); 
            var leftpath:seq<Tree> :| isDescPath(leftpath, root.left); 
            Situation(leftpath, root);
            TreeHeightToPath(root.left, h-1);
            // var leftvalidpath: seq<Tree> :| validPath(leftvalidpath, root) && |leftvalidpath| == h - 2;
            DescPathToPath(leftpath, root.left);
            assert isPath(leftpath);
            assert isPath([root]+leftpath);
            assert validPath([root]+leftpath, root);
            // assert |leftpath| == h-2;
            // assert |[root]+leftpath| == h-1;
            assert exists path: seq<Tree> :: validPath(path, root);
        } else if TreeHeight(root.left) <= TreeHeight(root.right) && TreeHeight(root.right) == h - 1 {
            assert root.right != Nil;
            TreeHeightToDescPath(root.right, h-1);
            var rightpath:seq<Tree> :| isDescPath(rightpath, root.right); 
            SituationR(rightpath, root);
            TreeHeightToPath(root.right, h-1);
            DescPathToPath(rightpath, root.right);
            assert validPath([root]+rightpath, root);
            assert isPath(rightpath);
            assert exists path: seq<Tree> :: validPath(path, root);
        } else{
            assert false;
        }
    }
}

method {:verify false} diameter(root: Tree) returns (heightDim: (int, int))
    ensures heightDim.0 == TreeHeight(root)
    ensures root != Nil ==> exists path: seq<Tree> :: isPath(path) && |path| - 1 == heightDim.1 && forall node :: node in path ==> node in TreeSet(root)
{
    if root == Nil {
        return (-1, -1);
    }
    if root.left == Nil && root.right == Nil {
        ghost var path := [root];
        // assert isPath(path) && |path| - 1 == 0;
        return (0,0);
    }
    var leftDiameter := diameter(root.left);
    var rightDiameter := diameter(root.right);
    var height := max(leftDiameter.0, rightDiameter.0) + 1;
    var dim := leftDiameter.0 + rightDiameter.0 + 2;
    var maxDiameter := max(leftDiameter.1, max(rightDiameter.1, dim));
    return (height, maxDiameter);
}

method diameterOfBinaryTree(root: Tree) returns (maxDiameter: int)

{
    var result := diameter(root);
    maxDiameter := result.1;
}