// T006: Ensure busy goes high in next clock cycle after start
property T006;
    @(posedge clk) disable iff (!rst_n | busy) $rose(start) |=> $rose(busy);
endproperty
ASSERT_T006: assert property (T006)
    else $error("ASSERT ", $sformatf("Error T006"));

// T007: Ensure cs_n asserts in next clock cycle after start
property T007;
    @(posedge clk) disable iff (!rst_n | busy) $rose(start) |=> $fell(cs_n);
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
    @(posedge sclk) disable iff (!rst_n) ($past(cs_n) && !cs_n) |-> (!cs_n) [*8];
endproperty
ASSERT_T010: assert property (T010)
    else $error("ASSERT ", $sformatf("Error T010"));

// T014: Ensure MISO only sampled on falling sclk edges 
property T014A; 
    @(posedge sclk) disable iff (!rst_n) (busy) |-> (rx_reg === $past(rx_reg));
endproperty
property T014B; 
    @(negedge sclk) disable iff (!rst_n) (busy) |-> (rx_reg !== $past(rx_reg));
endproperty
ASSERT_T014A: assert property (T014A)
    else $error("ASSERT ", $sformatf("Error T014A"));
ASSERT_T014B: assert property (T014B)
    else $error("ASSERT ", $sformatf("Error T014B"));

// TODO: since rx is fixed to B9, will not change wor
// T016: Ensure both RX and done udpate at same clock cycle 
property T016;
    @(edge clk) disable iff (!rst_n) $rose(done) |-> ($fell(rx_data) || $rose(rx_data));
endproperty
ASSERT_T016: assert property (T016)
    else $error("ASSERT ", $sformatf("Error T016"));
