/*
All items inside automatic tasks are allocated dynamically for each invocation and not shared between invocations of the same task running concurrently. 
Note that automatic task items cannot be accessed by hierarchical references.
If the task is made automatic, each invocation of the task is allocated a different space in simulation memory and behaves differently.
*/

module tb;

  initial display();
  initial display();
  initial display();
  initial display();

  // Note that the task is now automatic
  // The keyword automatic will make the task reentrant, otherwise it will be static by default.
  task automatic display();
    integer i = 0;
    i = i + 1;
    $display("i=%0d", i);
  endtask
endmodule

/*
  i=1
  i=1
  i=1
  i=1
*/

/*
變數的宣告週期
  sv 中資料的生命週期分為動態 (automatic) 和靜態 (static)。
  局部變數的生命週期與其所在域共存亡，也就是在 function/task 中的臨時變量，在其被呼叫結束後，臨時變數的生命週期也將終結。
  全域變數在程式執行開始到結束一直存在。
  如果資料變數被宣告為 automatic，那麼在進入該流程/方法後，automatic 變數會被創建，離開該行程/方法後，automatic 變數被銷毀。
  而 static 在模擬開始時被創建，而在進程/方法執行過程中，不會被銷毀，並且可以被多個進程和方法所共享。
  module 內全部是靜態變量，代表真實的電路結構。
  對於 automatic 方法，其內部所有變數預設也是 automatic。
  對於 static 方法，其內部所有變數預設也是 static。
  對於 static 變量，宣告時應該對其做初始化，而初始化只會伴隨它的生命週期執行一次，不會隨著方法呼叫而多次初始化。
  在 module、program、interface 宣告的變量，以及其他在 task/function 之外聲明的變量，預設是靜態變量，存在於是整個仿真階段。
*/