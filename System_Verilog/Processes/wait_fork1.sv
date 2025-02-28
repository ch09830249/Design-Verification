module tb_top;

	initial begin
		// Fork off 3 sub-threads in parallel and the currently executing main thread
		// will finish when any of the 3 sub-threads have finished.
		fork

			// Thread1 : Will finish first at time 40ns
			#40 $display ("[%0t ns] Show #40 $display statement", $time);

			// Thread2 : Will finish at time 70ns
			begin
				#20 $display ("[%0t ns] Show #20 $display statement", $time);

				#50 $display ("[%0t ns] Show #50 $display statement", $time);
			end

			// Thread3 : Will finish at time 60ns
			#60 $display ("[%0t ns] TIMEOUT", $time);
		join_any

      	// Display as soon as the fork is done
      	$display ("[%0t ns] Fork join is done, wait fork to end", $time);

      	// Fork two more processes
      	fork
          #10 $display ("[%0t ns] Wait for 10", $time);
          #20 $display ("[%0t ns] Wait for 20", $time);
        join_any

      	// Wait until ALL forked processes are over
      	wait fork;
        $display ("[%0t ns] Fork join is over", $time);
   	end
endmodule

/*
	[20 ns] Show #20 $display statement
	[40 ns] Show #40 $display statement
	[40 ns] Fork join is done, wait fork to end
	[50 ns] Wait for 10
	[60 ns] TIMEOUT
	[60 ns] Wait for 20
	[70 ns] Show #50 $display statement
	[70 ns] Fork join is over		==>  還是會等到所有 fork 做完才做
*/