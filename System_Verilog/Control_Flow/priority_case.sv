module tb;
  bit [1:0] 	abc;

  initial begin
    abc = 0;

    // First match is executed
    priority case (abc)
      0 : $display ("Found to be 0");
      0 : $display ("Again found to be 0");
      2 : $display ("Found to be 2");
    endcase
  end
endmodule

/*
  Found to be 0
*/