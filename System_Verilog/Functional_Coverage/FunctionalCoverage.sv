/*
  每個 cover point 去算出機率, 再將 cover group 內的所有 cover point 去做平均
*/

/*
  Variables are mentioned as a coverpoint.
  Coverpoints are put together in a covergroup block.
  Multiple covergroups can be created to sample the same variables with different set of bins
  bins are said to be "hit/covered" when the variable reaches the corresponding values. So, the bin featureB is hit when mode takes either 1,2 or 3.
  bin reserve is a single bin for all values that do not fall under the other bins.
  common will have 12 separate bins, one for each value from 0x4 to 0xF.
*/

class myTrns;
	rand bit [3:0] 	mode;   // 有 16 種可能的值 0~15
	rand bit [1:0] 	key;    // 有 4 種可能的值 0~3

   function display ();
      $display ("[%0tns] mode = 0x%0h, key = 0x%0h", $time, mode, key);
   endfunction

	covergroup CovGrp;
		coverpoint mode {
			bins featureA 	= {0};      // 0 為一個 bin
			bins featureB 	= {[1:3]};  // 1~3 為一個 bin
			bins common [] 	= {4:$};    // 4~Max_vaule 每個值各自為一個 bin
			bins reserve	= default;
		}
		coverpoint key;
	endgroup
endclass

// How to specify when to sample?
  // 手動 sample
    class myCov;
      covergroup CovGrp;
        ...
      endgroup

      function new ();
        CovGrp = new; 	        // Create an instance of the covergroup
      endfunction
    endclass

    module tb_top;
      myCov myCov0 = new ();   	// Create an instance of the class

      initial begin
        myCov0.CovGrp.sample ();
      end
    endmodule

  // 指定 sample 的時機
    covergroup CovGrp @ (posedge clk); 	// Sample coverpoints at posedge clk
    covergroup CovGrp @ (eventA); 			// eventA can be triggered with ->eventA;

// What are the ways to for conditional coverage?
  // 用 iff
    covergroup CovGrp;
      coverpoint mode iff (!_if.reset) {
          // bins for mode
      }
    endgroup
  // 或是用 .stop() 和 .start()
    CovGrp cg = new;
    initial begin
      #1 _if.reset = 0;
      cg.stop ();
      #10 _if.reset = 1;
      cg.start();
    end