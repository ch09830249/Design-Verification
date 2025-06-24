# uvm_component 中的 parent 參數
UVM 透過 uvm_component 來實現樹狀結構。所有的 UVM 樹的結點本質上都是一個 uvm_component。每個 uvm_component 都有一個特點：它們在 new 的時候，需要指定一個類型為 uvm_component、名字是 parent 的變數：
```
function new(string name, uvm_component parent);
```
# UVM 樹的根
UVM 是以樹的形式組織在一起的，作為一棵樹來說，其樹根在哪裡？其樹葉又是哪些呢？從第2章的例子來看，似乎樹根應該就是 uvm_test。在測試案例裡實例化 env，在 env 裡實例化 scoreboard、reference model、agent、在 agent 裡面實例化 sequencer、
driver 和 monitor。 scoreboard、reference model、sequencer、driver 和 monitor 都是樹的葉子，樹到此為止，沒有更多的葉子了。關於葉子的判斷是正確的，但是關於樹根的推論是錯誤的。
UVM 中真正的樹根是一個稱為 uvm_top 的東西
![image](https://github.com/user-attachments/assets/1de98988-7eee-4186-8e89-83247d2bdfdf)
