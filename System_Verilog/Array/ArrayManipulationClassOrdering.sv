/*
  Method	      Description
reverse()	  Reverses the order of elements in the array
sort()	    Sorts the array in ascending order, optionally using with clause        with 用於 class, 後面會有例子
rsort()	    Sorts the array in descending order, optionally using with clause
shuffle()	  Randomizes the order of the elements in the array. with clause is not allowed here.
*/

class Register;
  string name;
  rand bit [3:0] rank;
  rand bit [3:0] pages;

  function new (string name);
    this.name = name;
  endfunction

  function void print();
    $display("name=%s rank=%0d pages=%0d", name, rank, pages);
  endfunction

endclass

module tb;
  Register rt[4];
  string name_arr[4] = '{"alexa", "siri", "google home", "cortana"};

  initial begin
    $display ("
-------- Initial Values --------");
    foreach (rt[i]) begin
      rt[i] = new (name_arr[i]);
      rt[i].randomize();      // 隨機產生 rank 和 pages 值
      rt[i].print();
    end

    $display ("
--------- Sort by name ------------");

    rt.sort(x) with (x.name); // Rank name a~z
    foreach (rt[i]) rt[i].print();

    $display ("
--------- Sort by rank, pages -----------");

    rt.sort(x) with ( {x.rank, x.pages});
    foreach (rt[i]) rt[i].print();
  end
endmodule

/*

  -------- Initial Values --------
  name=alexa rank=12 pages=13
  name=siri rank=6 pages=12
  name=google home rank=12 pages=13
  name=cortana rank=7 pages=11

  --------- Sort by name ------------
  name=alexa rank=12 pages=13
  name=cortana rank=7 pages=11
  name=google home rank=12 pages=13
  name=siri rank=6 pages=12

  --------- Sort by rank, pages -----------
  name=siri rank=6 pages=12
  name=cortana rank=7 pages=11
  name=alexa rank=12 pages=13
  name=google home rank=12 pages=13
*/