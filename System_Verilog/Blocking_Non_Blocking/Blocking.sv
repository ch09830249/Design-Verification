/*
  Blocking assignment statements are assigned using = and are executed one after the other in a procedural block. 會一個 assign 完, 再 assign 下一個
  However, this will not prevent execution of statments that run in a parallel block.
*/

/*
  Note that there are two initial blocks which are executed in parallel when simulation starts. 
  Statements are executed sequentially in each block and both blocks finish at time 0ns. 
  To be more specific, variable a gets assigned first, followed by the display statement which is then followed by all other statements. 
  This is visible in the output where variable b and c are 8'hxx in the first display statement. 
  This is because variable b and c assignments have not been executed yet when the first $display is called.
*/
module tb;
  reg [7:0] a, b, c, d, e;

  initial begin
    a = 8'hDA;
    $display ("[%0t] a=0x%0h b=0x%0h c=0x%0h", $time, a, b, c);
    b = 8'hF1;
    $display ("[%0t] a=0x%0h b=0x%0h c=0x%0h", $time, a, b, c);
    c = 8'h30;
    $display ("[%0t] a=0x%0h b=0x%0h c=0x%0h", $time, a, b, c);
  end

  initial begin
    d = 8'hAA;
    $display ("[%0t] d=0x%0h e=0x%0h", $time, d, e);
 	  e = 8'h55;
    $display ("[%0t] d=0x%0h e=0x%0h", $time, d, e);
  end
endmodule

/*
  [0] a=0xda b=0xxx c=0xxx
  [0] a=0xda b=0xf1 c=0xxx
  [0] a=0xda b=0xf1 c=0x30
  [0] d=0xaa e=0xxx
  [0] d=0xaa e=0x55
*/