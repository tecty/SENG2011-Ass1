method IsClean(a: array<int>, key: int) returns (clean: bool) 
    ensures clean <==> forall k ::  0<= k < a.Length ==> a[k] != key
{
    clean := true ;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant clean == forall j :: 0<= j < i ==> a[j] != key
        decreases a.Length - i 
    {
        if (a[i] == key){
            // this array is not clean
            // break and has no need to search next
            clean := false;
            break;
        }

        i := i +1;
    }
}


method Test(){
    var a:= new int[5];
    a[0] := 1;
    a[1] := 2;
    a[2] := 2;
    a[3] := 2;
    a[4] := 3;
    var b:=  IsClean(a, 1);
    assert b;
    b:= IsClean(a, 2);
    assert b;
    b:= IsClean(a, 3);
    assert b;
}