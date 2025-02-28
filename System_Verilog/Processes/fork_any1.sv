module tb;
	initial begin
      $display ("[%0t] Main Thread: Fork join going to start", $time);
		fork
         // Thread1
         print (20, "Thread1");
         // Thread2
         print (30, "Thread2");
         // Thread3
         print (10, "Thread3");
      join_any
      $display ("[%0t] Main Thread: Fork join has finished", $time);
	end

  // Note that this task needs to be automatic
  task automatic print (int _time, string t_name);
    #(_time) $display ("[%0t] %s", $time, t_name);
  endtask
endmodule

/*
   [0] Main Thread: Fork join going to start
   [10] Thread3
   [10] Main Thread: Fork join has finished
   [20] Thread1
   [30] Thread2
*/