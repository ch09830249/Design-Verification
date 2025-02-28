/*
  Enumerated types are strongly typed and hence a variable of type enum cannot be assigned an integer value that lie outside the enumeration set unless an explicit cast is used.
*/
typedef enum bit [1:0] {RED, YELLOW, GREEN} e_light;

module tb;
  e_light light;

  initial begin
  	light = GREEN;
  	$display ("light = %s", light.name());

  	// Invalid because of strict typing rules
  	light = 0;
  	$display ("light = %s", light.name());

  	// OK when explicitly cast
    light = e_light'(1);
  	$display ("light = %s", light.name());

  	// OK. light is auto-cast to integer
    if (light == RED | light == 2)
    	$display ("light is now %s", light.name());

  end
endmodule

/*
  EnumTypeCheck.sv:11: error: This assignment requires an explicit cast.
  1 error(s) during elaboration.
*/