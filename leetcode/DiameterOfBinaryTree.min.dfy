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