# APB 協議的斷言檢查
![image](https://github.com/user-attachments/assets/cf81d057-6f20-4dbf-adff-cc4e623ee738)  
![image](https://github.com/user-attachments/assets/026044e0-0151-4df1-8c31-e6330f34347b)  
## 在 PSEL 拉高時, PADDR 總線不可為 X 值
```
property p_paddr_no_x;
  @(posedge clk) psel |-> !$isunknown(paddr);
endproperty: p_paddr_no_x
assert property(p_paddr_no_x)
```
## 在 PSEL 拉高的下一個週期, PENABLE 也應該拉高
```
property p_psel_rose_next_cycle_penable_rise;
  @(posedge clk) $rose(psel) |=> $rose(penable);
endproperty: p_psel_rose_next_cycle_penable_rise
assert property(p_psel_rose_next_cycle_penable_rise)
```
## 在 PENABLE 拉高的下一個週期, PENABLE 應該拉低
```
property p_penable_rose_next_cycle_fall;
  @(posedge clk) $rose(penable) |=> $fell(penable);
endproperty: p_penable_rose_next_cycle_fall
assert property(p_penable_rose_next_cycle_fall)
```
## 在 PSEL 和 PWRITE 同時保持為高的階段, PWDATA 需保持 (不該發生變化)
```
property p_pwdata_stable_during_trans_phase;
  @(posedge clk) ((psel && !penable) ##1 (psel && penable)) |=> $stable(pwdata);
endproperty: p_pwdata_stable_during_trans_phase
assert property(p_pwdata_stable_during_trans_phase)
```
## 在下一次傳輸開始前, 上一次的 PADDR 和 PWRITE 信號應該保持不變 (Todo)
```
property p_paddr_stable_until_next_trans;
  @(posedge clk) ((psel && !penable) ##1 (psel && penable)) |=> $stable(pwdata);
endproperty: p_paddr_stable_until_next_trans
assert property(p_paddr_stable_until_next_trans)
```
```
property p_pwrite_stable_until_next_trans;
  @(posedge clk) ((psel && !penable) ##1 (psel && penable)) |=> $stable(pwdata);
endproperty: p_pwrite_stable_until_next_trans
assert property(p_pwrite_stable_until_next_trans)
```
## 在 PENABLE 拉高的同個週期, PRDATA 也應該發生變化
```
```
# APB 協議的斷言覆蓋率 (期望的時序有沒有發生).
## 在寫操作時, 分別發生連續寫和非連續寫
```
```
## 對同一個地址先做寫操作再不間隔做讀操作
```
```
## 對同一個地址做連續兩次寫操作再從中讀數據
```
```
## 在讀操作時, 分別發生連續讀和非連續讀
```
```
## 對同一個地址先做讀操作再不間隔做寫操作, 再不間隔做讀操作
```
```
