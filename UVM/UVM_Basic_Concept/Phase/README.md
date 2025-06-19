# Phases
* All testbench components are derived from **uvm_component** and are aware of the phase concept. Each component goes through a **pre-defined set of phases**, and it **cannot proceed to the next phase until all components finish their execution in the current phase (只有在完成當前的 phase, 才會進行下一個 phase 的進行)**. So UVM phases act as a **synchronizing mechanism in the life cycle of a simulation**.
* Because phases are defined as callbacks, classes derived from uvm_component can perform useful work in the callback phase method. Methods that do **not consume simulation time** are **functions** and methods that **consume simulation time** are **tasks**. All phases can be grouped into three categories:
  * Build time phases
  * Run time phases
  * Clean-Up phases  
![image](https://github.com/user-attachments/assets/95557858-122d-4add-b08d-cb5e6a49d7cd)
## 為甚麼要引入這 12 個小的 phase? 
* 分成小的 phase 是為了實現更精細的控制
* reset、configure、main、shutdown 四個 phase 是核心,這四個 phase 通常模擬 DUT 的正常運作方式
式:  
(1)在 reset_phase 對 DUT 進行重設、初始化等操作  
(2)在 configure_phase 則進行 DUT 的設定  
(3)在 main_phase 主要是 DUT 的運行  
(4)在 shutdown_phase 主要是一些與 DUT 斷電相關的操作  
透過這種細分實現對 DUT 更加精確的控制,同時也讓我們實現在 phase 間的跳轉,更方便建構一些場景
## Main Phases
![image](https://github.com/user-attachments/assets/fecf14e8-1fe9-48f7-8ca0-4f7d401f376a)
* Logically, the first thing to be done is to **create testbench component objects so that they can be connected together**. This is the reason for the **build_phase**. It is better to not start connecting them while other testbench components are still building their sub-components. So we have **connect_phase** which will **connect all the components that were built in the previous phase**. Although the next two phases are rarely used or are typically used to display UVM hierhachy information. **Test stimulus is driven to the design during the run_phase** which is launched in parallel with other run-time phases that are described shown below.
## Run Phase
![image](https://github.com/user-attachments/assets/50093c74-7c51-4b16-8591-fd69b7b7aba0)
## What should be done in each UVM phase?
![image](https://github.com/user-attachments/assets/6311aca1-4b27-4f5c-aaec-1031873b1590)
![image](https://github.com/user-attachments/assets/c1e11624-55df-4918-bb67-09f895d40b60)
![image](https://github.com/user-attachments/assets/695ac27c-2d21-4d96-98d7-ce7a126bca01)
