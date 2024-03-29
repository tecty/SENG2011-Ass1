predicate Clean(a: array<int>, key: int) 
    reads a 
{
    forall k ::0<= k < a.Length ==> a[k] != key
}

method IsClean(a: array<int>, key: int) returns (clean: bool) 
    ensures clean <==> Clean(a,key)
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
        var a:= new int[5][1,2,2,2,3];
        assert a[0] == 1;
        assert a[1] == 2;
        assert a[2] == 2;
        assert a[3] == 2;
        assert a[4] == 3;

        var b:=  IsClean(a, 5);
        assert b==true;
        b:= IsClean(a, 2);
        assert !b;
        b:= IsClean(a, 3);
        assert !b;
        b:= IsClean(a, 4);
        assert b;

        var c:= new int[1][1];
        assert c[0]== 1;
        b:= IsClean(c,1);
        assert !b;
        b:= IsClean(c,2);
        assert b;

        var d:= new int[0][];
        b:= IsClean(d,1);
        assert b;
    }