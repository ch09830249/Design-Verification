# UVM Object
## What is UVM Object?
All components and object classes in a UVM environment are derived from uvm_object base class. The primary role of uvm_object class is to **define a set of common utility functions** like **print, copy, compare and record** which can be availed by any other class in a UVM testbench to save effort.
## Class Hierarchy
![image](https://github.com/user-attachments/assets/ee9fc7f0-9976-4dfb-a84f-c3b34ea62051)
## Class Definition
```
virtual class uvm_object extends uvm_void;

	// Creates a new uvm_object with the given name, empty by default
	function new(string name="");

	// Utility functions
	function void print (uvm_printer printer=null);
 	function void copy (uvm_object rhs, uvm_copier copier=null);
  function bit  compare (uvm_object rhs, uvm_comparer comparer=null);
 	function void record (uvm_recorder recorder=null);
	...

	// These two functions have to be redefined by child classes
  	virtual function uvm_object create (string name=""); return null; endfunction
  	virtual function string get_type_name (); return ""; endfunction

endclass
```
Classes that derive from uvm_object must implement the pure virtual methods such as **create** and **get_type_name**.  
(繼承自 uvm_object 都需實作上述兩個 pure virtual function, 否則無法實例化)  
These are taken care of by the inclusion of macros as set forth by the UVM coding guidelines.

The create method allocates **a new object of the same type as this object** and **returns it via the base uvm_object handle**.  
(以下案例, 實例化 my_object 物件, 回傳 uvm_object handle)  
* **Create**: The difference between new and create is that the former allocates memory for the current object whereas the latter **returns the handle for a different object allocated elsewhere**.
```
class my_object extends uvm_object;
	...

	// Implementation : Create an object of the new class type and return it
	virtual function uvm_object create(string name="my_object");
		my_object obj = new(name);
		return obj;
	endfunction

endclass
```
* **get_type_name**: function returns the class type name of the object and is used for debugging functions and by the UVM factory to create objects of a particular type.
```
class my_object extends uvm_object;

	// This static method is used to access via scope operator ::
	// without having to create an object of the class
	static function string type_name();
		return "my_object";
	endfunction

	virtual function string get_type_name();
		return type_name;
	endfunction
endclass
```
## Factory Interface
UVM employs a new concept called factory where all classes that are **defined in the UVM environment** are **registered with this "factory"**, which can then return an object of any requested class type later on. User classes are expected to include certain macros within them that allow it to be registered with the factory.
```
// An object derived from uvm_object by itself does not get
// registered with the UVM factory unless the macro is called
// within the class definition

class my_object extends uvm_object;

    // Register current object type with the factory
	`uvm_object_utils (my_object)  // 註冊該 object 到 factory

   ...

endclass
```
## Utility Functions
* **Print**
```
function void print(uvm_printer printer = null);
```
The print method **deep-prints the current object's variables** in a format determined by the UVM printer policy. As this function is not declared as virtual, **it cannot be overridden by a child class for a different implementation**. However, there is a hook/call-back function called **do_print to add custom information**.
* **Copy**
```
function void uvm_object::copy (uvm_object rhs, uvm_copier copier=null);
```
Like the print method above, **copy cannot be overridden** and to copy fields of a derived class, hat class should **override do_copy method** instead.
* **Compare**
```
function bit compare (uvm_object rhs, uvm_comparer comparer=null);
```
This method performs a **deep compare on members of this data object** with those of the object provided as an argument to this method, **returning a 1 on match and 0 otherwise**. This method cannot be overridden and custom code can be added to the user-definable hook called do_compare.  
  
In short, **uvm_object class is the parent class for other fundamental UVM classes**, such as **uvm_sequence_item (for transactions)** and **uvm_component (for testbench components)**. By inheriting from uvm_object, these classes inherit the essential functionalities and properties discussed above, making it a crucial building block for UVM verification environments.
