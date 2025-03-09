/*
  The bins construct allows the creation of a separate bin for each value in the given range of possible values of a coverage point variable.
  針對 cover point 的所有可能值去做切分
*/
/*
  EX:
    coverpoint mode {
      // Manually create a separate bin for each value
      bins zero = {0};
      bins one  = {1};

      // Allow SystemVerilog to automatically create separate bins for each value   // 自動為每個值都生成一個 bin
      // Values from 0 to maximum possible value is split into separate bins
      bins range[] = {[0:$]};

      // Create automatic bins for both the given ranges  // 2~3 兩個 bins, 5~7 三個 bins
      bins c[] = { [2:3], [5:7]};

      // Use fixed number of automatic bins. Entire range is broken up into 4 bins  // 所有可能的值, 平均切成 4 個 bins
      bins range[4] = {[0:$]};

      // If the number of bins cannot be equally divided for the given range, then
      // the last bin will include remaining items; Here there are 13 values to be
      // distributed into 4 bins which yields:        1. 先將所有值放在一起 {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 3, 6}  2. 切分 4 等分 13/4=3.... (所以每個 bin 有三個元素)
      // [1,2,3] [4,5,6] [7,8,9] [10, 1, 3, 6]
      bins range[4] = {[1:10], 1, 3, 6};

      // A single bin to store all other values that don't belong to any other bin  // 不屬於 cover points 中的任何一個 bin, 這些 values 屬於該 bin (default), 這裡不會算到 percentage
      bins others = default;
    }
*/

module tb;
  bit [2:0] mode; //

  // This covergroup does not get sample automatically because    // 因為沒有給 cover group sample 的時機, 所以需要手動 sample
  // the sample event is missing in declaration
  covergroup cg;
    coverpoint mode {
    	bins one = {1};
    	bins five = {5};
    }
  endgroup

  // Stimulus : Simply randomize mode to have different values and
  // manually sample each time
  initial begin
    cg cg_inst = new();
    for (int i = 0; i < 5; i++) begin
	  #10 mode = $random;
      $display ("[%0t] mode = 0x%0h", $time, mode);
      cg_inst.sample(); // 手動 sample
    end
    $display ("Coverage = %0.2f %%", cg_inst.get_inst_coverage());
  end

endmodule

/*
  [10] mode = 0x4
  [20] mode = 0x1
  [30] mode = 0x1
  [40] mode = 0x3
  [50] mode = 0x5
  Coverage = 100.00 %   因為兩個 bin 都 sample 到了, 所以 100%
*/

covergroup cg;
  coverpoint mode {

    // Declares a separate bin for each values -> Here there will 8 bins
    bins range[] = {[0:$]}; // 每個 value 各自一個 bin
  }
endgroup

/*
  [10] mode = 0x4
  [20] mode = 0x1
  [30] mode = 0x1
  [40] mode = 0x3
  [50] mode = 0x5
  Coverage = 50.00 %  // 4/8 (1, 3, 4, 5)
*/

covergroup cg;
  coverpoint mode {

    // Declares 4 bins for the total range of 8 values
    // So bin0->[0:1] bin1->[2:3] bin2->[4:5] bin3->[6:7]
    bins range[4] = {[0:$]};
  }
endgroup

/*
  [10] mode = 0x4
  [20] mode = 0x1
  [30] mode = 0x1
  [40] mode = 0x3
  [50] mode = 0x5
  Coverage = 75.00 %    // 3/4 (Hit bin0/1/2)
*/

covergroup cg;
  coverpoint mode {

    // Defines 3 bins
    // Two bins for values from 1:4, and one bin for value 7
    // bin1->[1,2] bin2->[3,4], bin3->7
    bins range[3] = {[1:4], 7};
  }
endgroup

/*
  [10] mode = 0x4
  [20] mode = 0x1
  [30] mode = 0x1
  [40] mode = 0x3
  [50] mode = 0x5
  Coverage = 66.67 %    // 2/3 (Hit bin1/2)
*/


/*
  特別注意 "[]"
  bins b_2to5 = {[2:5]};       => 這是將 2~5 為同一個 bin, 總共 1 個 bin
  bins b_2to5[] = {[2:5]};     => 這是 2~5 各自一個 bin, 總共 4 個 bins
  bins b_2to5[2] = {[2:5]};    => 這是 2~3 一個 bin, 4~5 一個 bin, 總共 2 個 bins
*/

/*
  ignore_bins b_6to7 = {[6:7]};   => 可忽略的值
  illegal_bins b_6to7 = {[6:7]};  => 非法值, simulation 會停止
*/

/*
  bins b0then1 = (0=>1);          => 從 0 變 1
  bins b2then3or4 = (2=>3,4);     => 從 2 變 3 或 4
*/

/*
  wildcard bins b_odd = {3'b??1}; => 奇數
*/