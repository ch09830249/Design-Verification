/*
  clocking block 是為了避免 test bench 跟 DUT 搶訊號造成 race condition

  A clocking block called ck1 is created which will be active on the positive edge of clk   // Clocking 就是對 signal 何時 sample 和 driven 去做更進一步的描述 (提早或延遲該時間)
    By default, 
      all input signals within the clocking block will be sampled "5ns before" and
      all output signals within the clocking block will be driven "2ns after"
          the positive edge of the clock clk data,
    valid and ready are declared as inputs to the block and hence will be sampled 5ns before the posedge of clk
    grant is an output signal to the block with its own time requirement. 
    Here grant will be driven at the negedge of clk instead of the default posedge.
*/

/*
  The delay_value represents a skew of how many time units away from the clock event a signal is to be sampled or driven. 3
  If a default skew is not specified, then all input signals will be sampled #1step and output signlas driven 0ns after the specified event.
*/

clocking ck1 @ (posedge clk);
	default input #5ns output #2ns;               // Default: positive edge 前 5ns sample (input), 後 2ns driven (output)
	input data, valid, ready = top.ele.ready;     // 沒特別另外說明就是跟著 default
	output negedge grant;                         // 有指定 grant 於 negedge driven
  // An input skew of 1step indicates that the signal should be sampled at the end of the previous time step, or in other words, immediately before the positive clock edge.
	input #1step addr;
endclocking

/*
  Signal req is specified to have a skew of 1ps and will be sampled "1 ps before" the clock edge clk. 
  The output signal gnt will be driven 2 ps/ns after the clock edge (Basedon the timescale). 
  The last signal sig is of inout type and will be sampled "1 ns before" the clock edge and driven "3 ns after" the clock edge.
*/

clocking cb @(clk);
    input  #1ps req;
    output #2 	gnt;
    input  #1 output #3 sig;
endclocking

/*
  An input skew of 1step indicates that the signal should be sampled at the end of the previous time step, 
  or in other words, immediately before the positive clock edge.

  Inputs with explicit #0 skew will be sampled at the same time as their corresponding clocking event, 
  but in the Observed region to avoid race conditions. Similarly, 
  outputs with no skew or explicit #0 will be driven at the same time as the clocking event, in the Re-NBA region.
*/

clocking cb @(posedge clk);
	input #1step req;
endclocking