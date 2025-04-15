![image](https://github.com/user-attachments/assets/87e98da5-67cc-4f8f-b367-67cabacb2f27)
# What is UVM (Universal Verification Methodology)?
* A standardized methodology for **verifying digital designs and systems-on-chip (SoCs)** in the semiconductor industry
* UVM is built on top of the **SystemVerilog** language and provides a framework for **creating modular**, **reusable testbench components** that can be easily integrated into the design verification process
# UVM 有什麼優缺點?
* UVM的優點
  * UVM 有各個機制、促進驗證平台的標準化
  * UVM 中 test sequence 和驗證平台是隔離獨立的,可以更好的控制激勵而不需要重新設計 agent
  * 改變 test sequence 可以簡單高校提高程式碼覆蓋率。
  * UVM支援工業標準,這會促進驗證平台標準化。
  * 此外,UVM透透過OOP(物件導向程式設計)的特點(例如繼承)以及使用覆蓋組件提高了重複使用率。
  * 因此 UVM 環境方便移植,架構清晰,組件連接方便,有利於進行大規模的驗證
2.UVM 的缺點:程式碼冗餘,工作量大,運作速度有缺失。
# What was used before UVM?
* **OVM (Open Verification Methodology)** was introduced in 2008 as an open-source verification methodology for digital designs and systems-on-chip (SoCs) and was based on SystemVerilog
* UVM was introduced in 2011 as **a successor to OVM**, and it built upon the concepts and principles of OVM. UVM was designed to be a **more standardized** and **flexible methodology** that could be easily adapted to different verification environments and use cases.

# Why was OVM replaced by UVM?
## Standardization
OVM was an open-source methodology that **lacked a formal standard**, which made it difficult for different organizations and tools to interoperate effectively. UVM was designed to be a **more standardized methodology**, with a **well-defined standard** that could be adopted by the entire semiconductor industry.
## Flexibility
OVM was designed primarily for **transaction-level modeling (TLM)**, which limited its applicability to other verification scenarios, such as register-transfer level (RTL) modeling. UVM was designed to be more flexible, with support for both **TLM and RTL modeling**, as well as other verification scenarios.
## Reusability
OVM provided a set of pre-defined classes and components for creating testbenches, but these components were not always modular and reusable. UVM was designed to be more modular and reusable, with a clear separation between testbench components and the design-under-test (DUT).
## Maintainability
OVM was not always easy to maintain or update, as changes to the methodology could affect existing testbenches and components. UVM was designed to be more maintainable, with a clear separation between the methodology and the implementation of testbenches and components.

# What does UVM contain?
It contains a set of pre-defined classes and methods that enable users to create modular, reusable testbench components for verifying digital designs and systems-on-chip (SoCs). Some of the key components of UVM include:
![image](https://github.com/user-attachments/assets/cd7493e5-3ae9-4971-b0fc-14ba8e45b544)
## Testbench Components
UVM provides a set of base classes that can be extended to create testbench components, such as **drivers, monitors, scoreboards, and agents**.
## Transactions
Transactions are used to model the communication between the design-under-test (DUT) and the testbench. UVM provides a **transaction class that can be extended to create transaction objects that carry information between the DUT and the testbench**.
## Phases
UVM defines a set of simulation phases that enable users to control the order in which testbench components are **created**, **initialized**, and **executed**.
## Messaging and Reporting
UVM provides a messaging and reporting infrastructure that enables users to output information about the simulation, such as warnings, errors, and debug information. (uvm_info)
## Configuration
UVM provides a **configuration database** that allows users to **store and retrieve configuration information for testbench components**.
## Functional Coverage
UVM provides a mechanism for **tracking functional coverage**, which is used to ensure that the design has been thoroughly tested.
## Register Abstraction Layer
UVM provides a register abstraction layer (RAL) that simplifies the process of **creating and accessing register maps**.
