function Abs(x:int):int{
    // return the absolute value of x 
    if x<0 then -x else x
}


method IncDec(x: int, y: int) returns (sum: int)
    ensures sum == x + y
{
    sum := 0;
    var tmp_x , tmp_y := x,y;

    // use while to increment them 
    while tmp_x != 0 || tmp_y != 0
        invariant x + y == sum + tmp_x + tmp_y
        decreases Abs(tmp_x) 
        decreases Abs(tmp_y)
    {
        if tmp_x < 0{
            sum := sum - 1;
            tmp_x:= tmp_x +1;
        }
        else if tmp_x > 0{
            sum := sum + 1;
            tmp_x := tmp_x - 1;
        }
        if tmp_y < 0{
            sum := sum - 1;
            tmp_y:= tmp_y + 1;
        }
        else if tmp_y > 0{
            sum := sum + 1;
            tmp_y := tmp_y -1;
        }
    }
}

method Test(){
    var sum: int;
    // Tests
    sum := IncDec( 5, 15);
    assert sum ==  20;
    sum := IncDec( 5,-15);
    assert sum == -10;
    sum := IncDec( 5,  0);
    assert sum ==   5;
    sum := IncDec(-5, 15);
    assert sum ==  10;
    sum := IncDec(-5,-15);
    assert sum == -20;
    sum := IncDec(-5,  0);
    assert sum == - 5;

}