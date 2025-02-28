/*
  // Normal arrays -> a collection of variables of same data type
  int array [10];         // all elements are of int type
  bit [7:0] mem [256];    // all elements are of bit type

  // Structures -> a collection of variables of different data types
  struct {
    byte    val1;
    int     val2;
    string  val3;
  } struct_name;

  struct {
	  [list of variables]
  } struct_name;

  Two types of structure
    - Unpacked Structure:   member 之間記憶體沒有連續
      1. A structure is unpacked by default and can be defined using the struct keyword and a list of member 
      declarations can be provided within the curly brackets followed by the name of the structure.

    - Packed Structure:     member 之間記憶體有連續
      1. A packed structure is a mechanism for subdividing a vector into fields that can be accessed as members
      and are packed together in memory without gaps.

      2. The first member in the structure is the most significant and subsequent members follow in decreasing order of significance.
*/

module tb;
    // 這裡宣告同時並創建一個該 structure
  	// Create a structure called "st_fruit"
	  // which to store the fruit's name, count and expiry date in days.
  	// Note: this structure declaration can also be placed outside the module
	struct {
  		string fruit;
  		int    count;
  		byte 	 expiry;
	} st_fruit;

  initial begin
    // st_fruit is a structure variable, so let's initialize it
    st_fruit = '{"apple", 4, 15};

    // Display the structure variable
    $display ("st_fruit = %p", st_fruit);

    // Change fruit to pineapple, and expiry to 7
    st_fruit.fruit = "pineapple";
    st_fruit.expiry = 7;
    $display ("st_fruit = %p", st_fruit);
  end
endmodule

/*
  Structure.sv:22: sorry: Unpacked structs not supported.
*/

/*
  st_fruit = '{fruit:"apple", count:4, expiry:'hf}
  st_fruit = '{fruit:"pineapple", count:4, expiry:'h7}
*/