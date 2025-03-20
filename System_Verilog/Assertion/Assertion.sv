/*
    The behavior of a system can be written as an assertion that should "be true at all times".       若是不滿足該條件, 中 assert
    Hence assertions are used to validate the behavior of a system defined as "properties",           將需要驗證的行為定義為 properties
    and can also be used in functional coverage.

    1. If a property of the design that is being checked for by an assertion does not behave in the expected way, 
       the assertion fails.        
       沒有依照預期的行為運作 => 中 assert
        
        For example, assume the design requests for grant and expects to receive an ack within the next four cycles. 
        But if the design gets an ack on the fifth cycle, the property that an ack should be returned within 4 clocks 
        is violated and the assertion fails.    
        預期 4 個 cycles 回傳 ack, 但是 5 個 cycles 才收到 ack => 中 assert

    2. If a property of the design that is being checked for by an assertion is forbidden from happening, 
       the assertion fails.   
       絕對禁止發生的事件發生了 => 中 assert     

        For example, assume a small processor decodes instructions read from memory, 
        encounters an unknown instruction and results in a fatal error. If such a scenario is never expected from the design, 
        the property of the design that only valid instructions can be read from memory is violated and the assertion fails.
        processor decodes 出來的指令為 unknown (禁止 invalid 指令) => 中 assert
*/

// A property written in Verilog/SystemVerilog
always @ (posedge clk) begin                    // 1. 檢查時機 (posedge clk)
	if (!(a && b))                              // 2. 要檢查的 expression
		$display ("Assertion failed");          // 3. true 就沒事, false 就中 Assert
end

// The property above written in SystemVerilog Assertions syntax
assert property(@(posedge clk) a && b);

/*
    Type	                                    Description
    assert	        To specify that the given property of the design is true in simulation
    assume	        To specify that the given property is an assumption and used by formal tools to generate input stimulus
    cover	        To evaluate the property for functional coverage
    restrict	    To specify the property as a constraint on formal verification computations and is ignored by simulators
*/

https://www.cnblogs.com/lyc-seu/p/12718412.html
https://www.cnblogs.com/gujiangtaoFuture/articles/10321384.html
https://zhuanlan.zhihu.com/p/38098913
