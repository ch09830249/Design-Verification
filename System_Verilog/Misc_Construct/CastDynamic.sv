/*
    When values need to be assigned between two different data type variables,  Dynamic 意思就是 runtime 才轉型
    ordinary assignment might not be valid and instead a system task called $cast should be used.

    $cast can be called as either a "task" or a "function", the difference being that when used as a function, 
    it returns a 1 if the cast is legal. It becomes useful in handling invalid assignments.    func 會回一個 return 值表示成功或失敗

    Syntax
        function int $cast (targ_var, source_exp);
        task $cast (targ_var, source_exp);

    When $cast is called as a task, it will attempt to assign the source expression to the target variable and 
    if it's invalid, a runtime error will occur and the target variable will remain unchanged.  
    若轉不成功, runtime 時才報錯 => 然後型態不變

    When $cast is called as a function, it will attempt to assign the source expression to the target variable and 
    return 1 if it succeeds. It does not make the assignment if it fails and returns 0.     
    Note that in this case there will be no runtime error, and the simulation will proceed with the unchanged value of the destination variable.
    若轉不成功, runtime 不會報錯 => 然後型態不變
*/

// 有轉型
typedef enum { PENNY=1, FIVECENTS=5, DIME=10, QUARTER=25, DOLLAR=100 } Cents;

module tb;
	Cents 	myCent;

	initial begin
		$cast (myCent, 10 + 5 + 10);
		$display ("Money=%s", myCent.name());
	end
endmodule

/*
    Money=QUARTER
*/

// 沒轉型
initial begin
	myCent = 10 + 5 + 10;
	...
end

// 不同環境有不同結果

// Aldec Riviera Pro    => 直接 compile error
/*
    ERROR VCP2694 "Assignment to enum variable from expression of different type." "testbench.sv" 7  1
    FAILURE "Compile failure 1 Errors 0 Warnings  Analysis time: 0[s]."
*/

// Cadence ncsim    => compile　warning, 然後照樣執行
/*
            myCent = 10 + 5 + 10;
                            |
    ncelab: *W,ENUMERR (./testbench.sv,7|18): This assignment is a violation of SystemVerilog strong typing rules for enumeration datatypes.

    ncsim> run
    Money=QUARTER
    ncsim: *W,RNQUIE: Simulation is complete.
    ncsim> exit
*/

// 轉型無效
// Task
initial begin
	$cast (myCent, 75);
	...
end
// runtime error
/*
    ncsim> run
            $cast (myCent, 75);
                |
    ncsim: *E,INVCST (./testbench.sv,7|6): Invalid cast: the source expression can not be cast to the type of the destination variable.
    Money=
    ncsim: *W,RNQUIE: Simulation is complete.
*/




// Function
initial begin
	if ($cast (myCent, 75))
		$display ("Cast passed");
	else
		$display ("Cast failed");
	...
end
// Completed without any runtime errors, and the target variable was left unchanged.
/*
    Cast failed
    Money=
    ncsim: *W,RNQUIE: Simulation is complete.
*/