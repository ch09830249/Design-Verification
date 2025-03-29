# What is a SystemVerilog interface ?
SystemVerilog interfaces are a way to create structured hierarchical connections between modules and blocks in a design. They provide a way to bundle signals and functionality into reusable components, which can be easily instantiated and connected in a design.

Modular design: Interfaces provide a modular approach to design, making it easier to create and reuse building blocks in a system.
Encapsulation: They help in encapsulating the functionality and signals inside a module or block, making it easier to understand and maintain.
Configurability: Interfaces can be parameterized, allowing for easy configurability and scalability.

# Difference between reg and logic.
Both reg and logic are used to store 4-state logic values that can be referenced later.  
The main difference is that logic signals can be used in both procedural and continuous assignments whereas reg can only be used in procedural code.

# Difference between :/ and := operators in randomization
Both operators are used in distribution constraints to assign weightage to different values in the distribution.

The :/ operator assigns the specified weight to the item, or if the item is a range, then the weight of each value is divided by N. The := operator assigns the specified weight to the item or if the item is a range, then to every value value in the range.

# How to disable randomization?
Randomization of variables can be disabled with rand_mode.
```
class ABC;
	rand bit [3:0] data;
endclass

module tb;
	initial begin
		ABC m_abc = new;
		m_abc.data.rand_mode(0); 	// Disable randomization

		m_abc.data.rand_mode(1); 	// Enable randomization
	end
endmodule
```

# Different types of code coverage.
Code coverage is a metric used to measure how well tests have exercised the design under test. It typically reports on the percentage of execution achieved across various dimensions of the design, such as statements, branches, and expressions, toggle, assertions and FSM.

# Write a constraint to detect odd numbers of ones in an 8-bit sequence.
Here's an example constraint that detects odd numbers of ones in an 8-bit sequence:
```
class ABC;
  rand bit [7:0] data;

  constraint c_data { $countones(data) % 2 != 0; }
endclass

module tb;
  initial begin
    ABC m_abc = new;

    for (byte i = 0; i < 20; i++) begin
      m_abc.randomize();
      $display("data = 0b%0b", m_abc.data);
    end
  end
endmodule
```

# What are local and protected access qualifiers?
A class member declared as local is available only to methods inside the class and are not visible within subclasses.
A class member declared as protected is available to methods inside the class and also to methods within subclasses.

# How does OOP concepts help in verification ?
Modular Design: Each module/class represents different aspects of the design. As a result, it becomes easier to develop a test bench by reusing and integrating these modular components. This saves time and effort in developing test cases and makes the system more scalable.
Encapsulation: Operations performed on any data object can be defined within the same class. For example, a function to pack a data array into a stream of 64 bit data.
Inheritance: Allows to create a base class and extend it with further derived classes. Common properties and methods are usually defined in base classes so that all subclasses have access and hence avoid code duplication
Polymorphism: Allows different implementations of the same method or function. Polymorphism helps to implement alternate test case scenarios without affecting the rest of the code significantly.

# What is a virtual interface ?
An interface is a collection of signals that allow connections to the DUT from the testbench. The handle to this interface is made available in classes by making it virtual. Hence a virtual interface is nothing but a handle that can hold a reference to the actual interface. Remember that an interface is declared at the testbench top level so that it can be passed to the DUT. So, rest of the components get access to this interface via a virtual interface.
```
class wishbone_monitor;
	virtual wishbone_if 	m_vif; 	// A virtual interface handle

	virtual task monitor;
		forever begin
			@(m_vif.clk);
			// Rest of the code
		end
	endtask
endclass
```

# Why logic was introduced in SV?
**logic is a new SystemVerilog data type**, when compared to Verilog which can be used in place of reg and wire in both procedural blocks and continuous assignments. (reg 用於 procedural blocks, wire 則是連續賦值)
logic 可以直接取代這兩個 data type, 放在 procedure block 內或是連續賦值皆可
It removes the hassle of having to redefine an existing signal as reg or wire depending on where it is used.

# Verilog中reg和wire的差別
* wire
  * wire 表示直通，即輸入有變化，輸出馬上無條件地反映（如與、非閘的簡單連接）
  * wire 相當於實體連線
  * wire 使用在連續賦值語句中 (線型資料需要持續的驅動)
    * 在連續賦值語句中，表達式右側的計算結果可以立即更新表達式的左側。在理解上，相當於一個邏輯之後直接連了一條線，這個邏輯對應於表達式的右側，而這條線就對應於 wire
  * wire 若無驅動器連接，其值為z
* reg
  * reg 表示一定要有觸發，輸出才會反映輸入的狀態
  * reg 相當於儲存單元
  * reg 表示一定要有觸發，沒有輸入的時候可以保持原來的值，但不直接實際的硬體電路對應 (暫存器型資料保持最後一次的賦值)
  * reg 則使用在過程賦值語句（initial ，always）中
    * 在過程賦值語句中，表達式右邊的計算結果在某種條件的觸發下放到一個變數當中，而這個變數可以宣告成reg類型的
    * 根據觸發條件的不同，過程賦值語句可以建模不同的硬體結構
      * 如果這個條件是時脈的上升沿或下降沿，那麼這個硬體模型就是一個觸發器
      * 如果這個條件是某一訊號的高電平或低電平，那麼這個硬體模型就是一個鎖存器
      * 如果這個條件是賦值語句的高電平或低電平，那麼這個硬體模型就是一個鎖存器
      * 如果這個條件是賦值語句右側一個硬體模型就是一個組合邏輯
  * reg預設初始值為不定值x
  
      對組合邏輯輸出變量，可以直接用assign。即如果不指定為reg類型，那麼就預設為1位元wire類型，故無需指定1位元wire類型的變數。當然專門指定出wire類型，可能是多位或為使程式易讀。wire只能被assign連續賦值，reg只能在initial和always中賦值。

      輸入埠可以由wire/reg驅動，但輸入埠只能是wire；輸出埠可以是wire/reg類型，輸出埠只能驅動wire ；若輸出埠在過程區塊中賦值則為reg型，若在過程區塊外賦值則為net型（wire/tri）。用關鍵字inout宣告一個雙向埠, inout埠不能宣告為reg類型，只能是wire型別。

      預設訊號是wire類型，reg類型要申明。這裡所說的預設是指輸出訊號申明成output時為wire。如果是模組內部訊號，必須申明成wire或reg.

      對always語句而言，賦值要申明成reg，連續賦值assign的時候要用wire。

 

模組呼叫時 訊號類型決定方法總結如下：

 

•訊號可分為連接埠訊號和內部訊號。出現在連接埠清單中的訊號是連接埠訊號，其它的訊號為內部訊號。

•對於連接埠訊號，輸入埠只能是net類型。輸出埠可以是net類型，也可以是register類型。若輸出埠在過程區塊中賦值則為register型別；若在過程區塊外賦值(包含實例化語句），則為net型別。

•內部訊號類型與輸出埠相同，可以是net或register類型。判斷方法也與輸出埠相同。若在過程區塊中賦值，則為register型別；若在過程區塊外賦值，則為net型別。

•若訊號既需要在過程區塊中賦值，又需要在過程區塊外賦值。這種情況是有可能出現的，如決斷訊號。這時需要一個中間訊號轉換。

 

 

下面所列是常出的錯誤及對應的錯誤訊息(error message)

•用過程語句給一個net類型的或忘記宣告類型的訊號賦值。

           訊息：illegal …… assignment.

•將實例的輸出連接到聲明為register類型的訊號。

           訊息：<name> has illegal output port specification.

•將模組的輸入訊號宣告為register類型。

           訊息：incompatible declaration, <signal name> …

 
