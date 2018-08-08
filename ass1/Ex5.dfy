predicate EOSorted(a: array<int>)
    reads a 
{
    a.Length >= 2 ==>  
    (forall j:: (2 <= j < a.Length && j%2 == 0) ==> a[j] >= a[j-2]) &&  
    (forall k:: (3 <= k < a.Length && k%2 == 1) ==> a[k] >= a[k-2])
}

predicate Sorted (a:array<int>)
reads a
{ forall j,k:: 0<=j<k<a.Length ==> a[j]<=a[k] }

method Test()
{
    var a:array<int> := new int[][];
    assert EOSorted(a);
    var b:array<int> := new int[][2,1,4,2,6,3];
    assert EOSorted(b);
    var c:array<int> := new int[][1,2,3,1];
    assert c[0]==1;
    assert c[1]==2;
    assert c[2]==3;
    assert c[3]==1;
    assert  !EOSorted(c);
    var d:array<int> := new int[][1,2,1,2,1];
    assert EOSorted(d);
    var e:array<int> := new int[][1,1,1,1,1];
    assert EOSorted(e);
    var f:array<int> := new int[][1,100,1,100,1,200];
    assert EOSorted(f);
    var g:array<int> := new int[][1,2,4,2,2,1,1];
    // assert g[0],g[1],g[2],g[3],g[4],g[5],g[6]== 1,2,4,2,2,1,1;
    // assert !EOSorted(g);
    // var h: array<int> := new int[][1,2,3,4,1];
    // assert !Sorted(h);
}