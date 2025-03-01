/*
unique and unique0 ensure that there is no overlapping case items and hence can be evaluated in parallel.   // 和 priority 差別是 unique 會平行運算 condition, priority 則是循序運算 condition
If there are overlapping case items, then a violation is reported.

    If more than one case item is found to match the given expression, then a violation is reported and the first matching expression is executed
    If no case item is found to match the given expression, then a violation is reported only for unqiue
*/

module tb;
  bit [1:0] 	abc;

  initial begin
    abc = 1;

    // None of the case items match the value in "abc"
    // A violation is reported here
    unique case (abc)
      0 : $display ("Found to be 0");
      2 : $display ("Found to be 2"); // 沒有一個成立
    endcase
  end
endmodule

/*
  ncsim: *W,NOCOND: Unique case violation:  Every case item expression was false.
              File: ./testbench.sv, line = 9, pos = 14
            Scope: tb
              Time: 0 FS + 1
*/

module tb;
  bit [1:0] 	abc;

  initial begin
    abc = 0;

    // Multiple case items match the value in "abc"
    // A violation is reported here
    unique case (abc)
      0 : $display ("Found to be 0");
      0 : $display ("Again found to be 0");
      2 : $display ("Found to be 2");
    endcase
  end
endmodule

/*
  Found to be 0   => 多個 condition 滿足, 會執行第一個滿足的, 再 report an error
  ncsim: *W,MCONDE: Unique case violation:  Multiple matching case item expressions at {line=10:pos=6 and line=11:pos=6}.
              File: ./testbench.sv, line = 9, pos = 14
            Scope: tb
              Time: 0 FS + 1
*/