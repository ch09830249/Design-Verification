module tb;
	initial begin
      $display ("[%0t] Main Thread: Fork join going to start", $time);
		fork
         // Thread 1
			fork
            // Thread 1_0
            #50 $display ("[%0t] Thread1_0 ...", $time);
            // Thread 1_1
            #70 $display ("[%0t] Thread1_1 ...", $time);
            // Thread 1_2
            begin
               #10 $display ("[%0t] Thread1_2 ...", $time);
               #100 $display ("[%0t] Thread1_2 finished", $time);
            end
         join

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
   [10] Thread1_2 ...
   [15] Thread2 finished
   [20] Thread3 finished
   [50] Thread1_0 ...
   [70] Thread1_1 ...
   [110] Thread1_2 finished
   [110] Main Thread: Fork join has finished
*/