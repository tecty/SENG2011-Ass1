predicate Occourance(a :array<int>, key: int, count: int, last:int)
requires 0 <= last < a.Length
decreases  a, count, last
{
    if(last > 0) then 
        if (a[last]== key)
        then 
            Occourance(a, key,count -1 , last -1)
        else 
            Occourance(a, key, count, last -1)
    else
        // last == 0 
        a[0] == key ==> count == 1 && a[0] != key ==> count == 0
}



method Just1(a: array<int>, key: int) returns (b: bool)
{
    var count:= 0;
    var i := 0;

    while (i < a.Length)
    
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