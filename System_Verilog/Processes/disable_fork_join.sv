/*
   All active threads that have been kicked off from a fork join block can be killed by calling disable fork.
*/

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
		$display ("[%0tns] Fork join is done", $time);
   end
endmodule

/*
   [20 ns] Show #20 $display statement
   [40 ns] Show #40 $display statement
   [40ns] Fork join is done
   [60 ns] TIMEOUT   ==> 明明做完了卻還是有 TIMEOUT 字樣
   [70 ns] Show #50 $display statement
*/