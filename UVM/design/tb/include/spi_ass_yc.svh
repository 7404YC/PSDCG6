// T006: Ensure busy goes high in next clock cycle after start
property T006;
    // @(posedge clk) (rst_n && !busy && $rose(start)) |=> $rose(busy) || !rst_n;
    @(posedge clk) disable iff (!rst_n) (!busy && $rose(start)) |=> $rose(busy);
endproperty
ASSERT_T006: assert property (T006)
    else $error("ASSERT ", $sformatf("Error T006"));

// T007: Ensure cs_n asserts in next clock cycle after start
property T007;
    @(posedge clk) disable iff (!rst_n ) (!busy && $rose(start)) |=> $fell(cs_n);
endproperty
ASSERT_T007: assert property (T007)
    else $error("ASSERT ", $sformatf("Error T007"));

// T008: Ensure cs_n should not glitch during transfer
property T008;
    @(edge clk) disable iff (!rst_n) !($rose(cs_n) && $fell(cs_n));
endproperty
ASSERT_T008: assert property (T008)
    else $error("ASSERT ", $sformatf("Error T008"));

// T009: Ensure cs_n low-to-high when done asserted
property T009;
    @(edge clk) disable iff (!rst_n) $rose(done) |-> $rose(cs_n);
endproperty
ASSERT_T009: assert property (T009)
    else $error("ASSERT ", $sformatf("Error T009"));

// T010: Ensure Ensure cs_n not deassert early      
property T010;
    @(edge sclk) /*disable iff (!rst_n)*/ $fell(cs_n) |-> (!cs_n)[*15];
endproperty
ASSERT_T010: assert property (T010)
    else $error("ASSERT ", $sformatf("Error T010"));

// T014: Ensure MISO only sampled on falling sclk edges 
// Shadow registers to hold value at last posedge and negedge
logic [7:0] rx_reg_at_posedge = 0;
logic [7:0] rx_reg_at_negedge = 0;
// Capture rx_reg at each posedge
always @(posedge sclk or negedge rst_n) begin
    #1;
    if (!rst_n)
        rx_reg_at_posedge <= '0;
    else
        rx_reg_at_posedge <= rx_reg;
end
// Capture rx_reg at each negedge
always @(negedge sclk or negedge rst_n) begin
    #1;
    if (!rst_n)
        rx_reg_at_negedge <= '0;
    else
        rx_reg_at_negedge <= rx_reg;
end
// T014A: On posedge, value should match last negedge's value
property T014A;
    @(posedge sclk) disable iff (!rst_n)
      (busy) && (rx_reg_at_negedge !== 0) |-> (rx_reg === rx_reg_at_negedge);
endproperty
// T014B: On negedge, value should differ from last posedge's value
logic sclk_dly;
always @(edge sclk) #1ps sclk_dly = sclk; // pulse delayed slightly
property T014B;
    @(negedge sclk_dly) disable iff (!rst_n)
      (busy) && (rx_reg_at_posedge !== 0) |-> (rx_reg !== rx_reg_at_posedge);
endproperty
// Assertions
ASSERT_T014A: assert property (T014A)
    else $error("ASSERT", "Error T014A");
ASSERT_T014B: assert property (T014B)
    else $error("ASSERT", "Error T014B");

// T016: Ensure both RX and done udpate at same clock cycle 
property T016;
    @(edge clk) disable iff (!rst_n) $rose(done) |-> ($fell(rx_data) || $rose(rx_data));
endproperty
ASSERT_T016: assert property (T016)
    else $error("ASSERT ", $sformatf("Error T016"));
