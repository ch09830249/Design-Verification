// A property written in Verilog/SystemVerilog
always @ (posedge clk) begin
	if (!(a && b))
		$display ("Assertion failed");
end

// The property above written in SystemVerilog Assertions syntax
assert property(@(posedge clk) a && b);

/* Type of Assertion Statements 
  Type	                            Description
  assert	  To specify that the given property of the design is true in simulation                                      該 property 在 simulation 時必須為 true
  assume	  To specify that the given property is an assumption and used by formal tools to generate input stimulus
  cover	    To evaluate the property for functional coverage                                                            計算該 property 出現次數
  restrict	To specify the property as a constraint on formal verification computations and is ignored by simulators
*/

/* Building Blocks of Assertions 

  Sequence
    A sequence of multiple logical events typically form the functionality of any design. 
    These events may span across multiple clocks or exist for just a single clock cycle. 
    To keep things simple, smaller events can be depicted using simple assertions which can then be used to build more complex behavior patterns.

    // Sequence syntax
    sequence <name_of_sequence>
      <test expression>
    endsequence

    // Assert the sequence
    assert property (<name_of_sequence>);

  Property
    These events can be represented as a sequence and a number of sequences can be combined to create more complex sequences or properties.
    It is necessary to include a clocking event inside a sequence or property in order to assert it.

    // Property syntax
    property <name_of_property>
      <test expression> or
      <sequence expressions>
    endproperty

    // Assert the property
    assert property (<name_of_property>);
*/

/*
  Immediate Assertion (非時序的, 執行時如同過程語句) => 我的理解是在仿真的過程檢查斷言  (EX: 在跑仿真過程, 根據預期行為來檢查斷言)
    Immediate assertions are executed like a statement in a procedural block and follow simulation event semantics. 
    These are used to verify an immediate property during simulation.
*/
always @ (<some_event>) begin
  ...
  // This is an immediate assertion executed only
  // at this point in the execution flow
  $assert(!fifo_empty);      // Assert that fifo is not empty at this point
  ...
end

/*
  Concurrent Assertion (時序的 (EX: 時脈邊緣激活), 變數的值為採樣的值, 與設計模組一同並行執行) => 我的理解是跟著 Design 去並行檢查斷言 (EX: 跟著某 interface 檢查 port 是否有照 SPEC)
    Concurrent assertions are based on clock semantics and use sampled values of their expressions. 
    Circuit behavior is described using SystemVerilog properties that gets evaluated everytime on the given clock and a failure in simulation indicates that 
    the described functional behavior got violated.
*/
// Define a property to specify that an ack should be
// returned for every grant within 1:4 clocks
property p_ack;
	@(posedge clk) gnt ##[1:4] ack;
endproperty

assert property(p_ack);    // Assert the given property is true always

/*
  Step 1: Create boolean expressions
  Step 2: Create sequence expressions
  Step 3: Create property
  Step 4: Assert property
*/

module tb;
  bit a, b, c, d;
  bit clk;

  always #10 clk = ~clk;

  initial begin
    for (int i = 0; i < 20; i++) begin
      {a, b, c, d} = $random;
      $display("%0t a=%0d b=%0d c=%0d d=%0d", $time, a, b, c, d);
      @(posedge clk);
    end
    #10 $finish;
  end

  sequence s_ab;
    a ##1 b;
  endsequence

  sequence s_cd;
    c ##2 d;
  endsequence

  property p_expr;
    @(posedge clk) s_ab ##1 s_cd;
  endproperty

  assert property (p_expr);
endmodule

/*
  Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Jan  8 05:02 2020
  Warning : License for product VCSRuntime_Net(725) will expire within 10 days, on: 17-jan-2020.

  If you would like to temporarily disable this message, set 
  the VCS_LIC_EXPIRE_WARNING environment variable to the number of days
  before expiration that you want this message to start (the minimum is 0).
  0 a=0 b=1 c=0 d=0
  10 a=0 b=0 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 10ns failed at 10ns
    Offending 'a'
  30 a=1 b=0 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 30ns failed at 30ns
    Offending 'a'
  50 a=0 b=0 c=1 d=1
  70 a=1 b=1 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 70ns failed at 70ns
    Offending 'a'
  "testbench.sv", 28: tb.unnamed$$_3: started at 50ns failed at 70ns
    Offending 'b'
  90 a=1 b=1 c=0 d=1
  110 a=0 b=1 c=0 d=1
  130 a=0 b=0 c=1 d=0
  "testbench.sv", 28: tb.unnamed$$_3: started at 130ns failed at 130ns
    Offending 'a'
  "testbench.sv", 28: tb.unnamed$$_3: started at 90ns failed at 130ns
    Offending 'c'
  150 a=0 b=0 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 150ns failed at 150ns
    Offending 'a'
  170 a=1 b=1 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 170ns failed at 170ns
    Offending 'a'
  190 a=0 b=1 c=1 d=0
  210 a=1 b=1 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 210ns failed at 210ns
    Offending 'a'
  230 a=1 b=1 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 190ns failed at 230ns
    Offending 'c'
  250 a=1 b=1 c=0 d=0
  270 a=1 b=0 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 230ns failed at 270ns
    Offending 'c'
  290 a=0 b=1 c=1 d=0
  "testbench.sv", 28: tb.unnamed$$_3: started at 270ns failed at 290ns
    Offending 'b'
  "testbench.sv", 28: tb.unnamed$$_3: started at 250ns failed at 290ns
    Offending 'c'
  310 a=0 b=1 c=0 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 310ns failed at 310ns
    Offending 'a'
  330 a=1 b=0 c=1 d=0
  "testbench.sv", 28: tb.unnamed$$_3: started at 330ns failed at 330ns
    Offending 'a'
  "testbench.sv", 28: tb.unnamed$$_3: started at 290ns failed at 330ns
    Offending 'c'
  350 a=0 b=1 c=0 d=1
  370 a=0 b=1 c=1 d=1
  "testbench.sv", 28: tb.unnamed$$_3: started at 370ns failed at 370ns
    Offending 'a'
  "testbench.sv", 28: tb.unnamed$$_3: started at 390ns failed at 390ns
    Offending 'a'
  $finish called from file "testbench.sv", line 13.
  $finish at simulation time                  400
            V C S   S i m u l a t i o n   R e p o r t 
*/