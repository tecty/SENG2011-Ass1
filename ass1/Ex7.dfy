function method doOccourance(a: array<int>, key: int, last:int):int
    requires 0 <= last < a.Length 
    decreases last
    reads a
{
    if (last == 0) then 
        if( a[last] == key) then 
            1
        else
            0
    else 
        if( a[last] == key) then 
            doOccourance(a,key,last -1) + 1
        else 
            doOccourance(a,key,last -1)
        
}


function method Occourance(a: array<int>, key: int):int
    reads a 
{
    if(a.Length == 0) then 
        0
    else 
        doOccourance(a,key, a.Length -1)
}

method Just1(a: array<int>, key: int) returns (b: bool)
    ensures b ==(1  == Occourance(a,key))
{
    var count:= 0;
    var i := 0;

    while (i < a.Length)
        invariant 0<= i <= a.Length
        // if statement in the loop inv 
        invariant 0 < i <= a.Length ==> count == doOccourance(a,key, i-1)
        invariant i == 0            ==> count == 0
        decreases a.Length - i 
    {
        if(a[i]== key){
            // count all the occourance of key in the array
            count := count +1;
        }
        i:= i+1;
    }
    // check whether count is 1 and return 
    b:= count ==1;
}