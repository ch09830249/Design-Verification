/*
Processes that use a semaphore must first get a key from the bucket before they can continue to execute. 
Other proceses must wait until keys are available in the bucket for them to use. 

semaphore 	[identifier_name];

Note that semaphore is a built-in class and hence it should be used just like any other class object. 
It has a few methods with which we can allocate the number of keys for that semaphore object, get and put keys into the bucket.

Name	                                    Description
function new (int keyCount = 0);	        Specifies number of keys initially allocated to the semaphore bucket
function void put (int keyCount = 1);	    Specifies the number of keys being returned to the semaphore
task get (int keyCount = 1);	            Specifies the number of keys to obtain from the semaphore
function int try_get (int keyCount = 1);	Specifies the required number of keys to obtain from the semaphore
*/

module tb_top;
   semaphore key;

   initial begin
      key = new (1); // 只有一把鑰匙
      fork
         personA ();
         personB ();
         #25 personA ();
      join_none
   end

   task getRoom (bit [1:0] id);
      $display ("[%0t] Trying to get a room for id[%0d] ...", $time, id);
      key.get (1);   // 沒拿到就會在這裡等, 直到拿到才會執行下一步
      $display ("[%0t] Room Key retrieved for id[%0d]", $time, id);
   endtask

   task putRoom (bit [1:0] id);
      $display ("[%0t] Leaving room id[%0d] ...", $time, id);
      key.put (1);
      $display ("[%0t] Room Key put back id[%0d]", $time, id);
   endtask

   task personA ();
      getRoom (1);
      #20 putRoom (1);
   endtask

   task personB ();
      #5  getRoom (2);
      #10 putRoom (2);
   endtask
endmodule

/*
   [0] Trying to get a room for id[1] ...
   [0] Room Key retrieved for id[1]
   [5] Trying to get a room for id[2] ...
   [20] Leaving room id[1] ...
   [20] Room Key put back id[1]
   [20] Room Key retrieved for id[2]
   [25] Trying to get a room for id[1] ...
   [30] Leaving room id[2] ...
   [30] Room Key put back id[2]
   [30] Room Key retrieved for id[1]
   [50] Leaving room id[1] ...
   [50] Room Key put back id[1]
*/