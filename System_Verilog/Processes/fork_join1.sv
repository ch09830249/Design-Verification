module tb;
	initial begin
      $display ("[%0t] Main Thread: Fork join going to start", $time);
		fork
			// Thread 1
			#30 $display ("[%0t] Thread1 finished", $time);

			// Thread 2
         begin
            #5 $display ("[%0t] Thread2 ...", $time);
            #10 $display ("[%0t] Thread2 finished", $time);
         end

         // Thread 3
			#20 $display ("[%0t] Thread3 finished", $time);
		join
      $display ("[%0t] Main Thread: Fork join has finished", $time);
	end
endmodule

/*
   [0] Main Thread: Fork join going to start
   [5] Thread2 ...
   [15] Thread2 finished
   [20] Thread3 finished
   [30] Thread1 finished
   [30] Main Thread: Fork join has finished
*/