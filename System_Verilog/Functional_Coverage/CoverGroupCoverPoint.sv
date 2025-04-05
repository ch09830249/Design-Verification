/*
  covergroup

    - A set of coverage points                // 要 cover 的變數
    - Cross coverage between coverage points  // 多個變數 cross 的數組
        EX: cx_ab: cross a, b;
    - An event that defines when the covergroup is sampled
        EX: covergroup cg @ (posedge clk);    // 只有在 posedge 採樣, 不用再透過 .sample() 採樣
    - Other options to configure coverage object  
        option.at_least: 該 cover point 至少要出現次數, 滿足才算 cover 到
        option.weight: 該 cover point 的權重, 最後在算該 cover group 的機率用加權平均
        option.auto_bin_max: 該所有可能的值區分最多幾個 interval (平均的區分)
        ...
*/

module tb;

  // Declare some variables that can be "sampled" in the covergroup
  bit [1:0] mode;
  bit [2:0] cfg;

  // Declare a clock to act as an event that can be used to sample
  // coverage points within the covergroup
  bit clk;
  always #20 clk = ~clk;

  // "cg" is a covergroup that is sampled at every posedge clk
  covergroup cg @ (posedge clk);        // 只有在 posedge 採樣, 不用再透過 .sample() 採樣
    coverpoint mode;                    // 這裡只 cover mode 這個變數
  endgroup

  // Create an instance of the covergroup
  cg  cg_inst;                          // 建立此 cover group 的 handle

  initial begin
    // Instantiate the covergroup object similar to a class object
    cg_inst= new();                     // 例化一個 cover group

    // Stimulus : Simply assign random values to the coverage variables
    // so that different values can be sampled by the covergroup object
    for (int i = 0; i < 5; i++) begin
      @(negedge clk);                   // 等 clk 變 negedge, 再做下面 random 的動作
      mode = $random;
      cfg  = $random;
      $display ("[%0t] mode=0x%0h cfg=0x%0h", $time, mode, cfg);
    end
  end

  // At the end of 500ns, terminate test and print collected coverage
  initial begin
    #500 $display ("Coverage = %0.2f %%", cg_inst.get_inst_coverage());
    $finish;
  end
endmodule

/*
  [40] mode=0x0 cfg=0x1       // 在 negedge assign values 並印出 value
  [80] mode=0x1 cfg=0x3
  [120] mode=0x1 cfg=0x5
  [160] mode=0x1 cfg=0x2
  [200] mode=0x1 cfg=0x5
  Coverage = 50.00 %          // mode 0~3 中只有 sample 出 0 和 1, 因此 50% coverage rate
*/



/*
  coverpoint

  A covergroup can contain one or more coverage points. 
  A coverpoint specifies an integral expression that is required to be covered. 
  Evaluation of the coverpoint expression happens when the covergroup is sampled. 
  The SystemVerilog coverage point can be optionally labeled with a colon :.

  The example shown below randomizes the two variables mode and cfg multiple times and is assigned a value on every negative edge of the clock. 
  The covergroup is specified to be sampled at every occurence of a positive edge of the clock. 
  So the two variables are randomized 5 times at the negative edge of the clock and sampled at the positive edge of the clock.


  mode can have values from 0 to 3 and cfg can have values from 0 to 7. 
  The question of coverage is this: How much of the total values each variable can have has actually happened ?
*/

module tb;

  bit [1:0] mode; // 0~3
  bit [2:0] cfg;  // 0~7

  bit clk;
  always #20 clk = ~clk;

  // "cg" is a covergroup that is sampled at every posedge clk
  // This covergroup has two coverage points, one to cover "mode"
  // and the other to cover "cfg". Mode can take any value from
  // 0 -> 3 and cfg can take any value from 0 -> 7
  covergroup cg @ (posedge clk);          // 只有在 posedge 採樣, 不用再透過 .sample() 採樣
    // Coverpoints can optionally have a name before a colon ":"    // 這只是取名而已, 之後會顯示在 report 上
    cp_mode    : coverpoint mode;         // mode 0~3
    cp_cfg_10  : coverpoint cfg[1:0];     // cfg 0~3
    cp_cfg_lsb : coverpoint cfg[0];       // cfg 0~1
    cp_sum     : coverpoint (mode + cfg); // mode + cfg 0~7   PS: 因為最多 3 個 bits, 所以不是 0~10
  endgroup

  cg  cg_inst;

  initial begin
    cg_inst= new();

    for (int i = 0; i < 5; i++) begin
      @(negedge clk);                     // 上沿採樣, 下沿指定新的隨機值
      mode = $random;
      cfg  = $random;
      $display ("[%0t] mode=0x%0h cfg=0x%0h", $time, mode, cfg);
    end
  end

  initial begin
    #500 $display ("Coverage = %0.2f %%", cg_inst.get_inst_coverage());
    $finish;
  end
endmodule

/*
  [40] mode=0x0 cfg=0x1   // (0b0001)     這裡最開始的 mode=0x0, cfg=0x1 (0b0000) 好像沒用印到
  [80] mode=0x1 cfg=0x3   // (0b0011)
  [120] mode=0x1 cfg=0x5  // (0b0101)
  [160] mode=0x1 cfg=0x2  // (0b0010)
  [200] mode=0x1 cfg=0x5  // (0b0101)
  Coverage = 78.12 %          
  /* 
    mode:       50%     2/2 (0b0, 0b1), 
    cp_cfg_10:  100%    4/4 (0b00, 00b01, 0b11, 0b10), 
    cp_cfg_lsb: 100%    2/2 (0b1, 0b0), 
    cp_sum:     62.5%   5/8 (0, 1, 4, 6, 3)
    (50% + 100% + 100% + 62.5%) / 4 = 78.125%
  */
*/