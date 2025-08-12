// T006: Ensure busy goes high in next clock cycle after start
property T006;
    @(posedge clk) $rose(start) |=> $rose(busy);
endproperty
assert property (T006)
    else $error("ASSERT", $sformatf("Error T006"));

// T007: Ensure cs_n asserts in next clock cycle after start
property T007;
    @(posedge clk) $rose(start) |=> $fell(cs_n);
endproperty
assert property (T007)
    else $error("ASSERT", $sformatf("Error T007"));

// T008: Ensure cs_n should not glitch during transfer
property T008;
    @(edge clk) !($rose(cs_n) && $fell(cs_n));
endproperty
assert property (T008)
    else $error("ASSERT", $sformatf("Error T008"));

// T009: Ensure cs_n low-to-high when done asserted
property T009;
    @(edge clk) $rose(done) |-> $rose(cs_n);
endproperty
assert property (T009)
    else $error("ASSERT", $sformatf("Error T009"));

// T010: Ensure Ensure cs_n not deassert early
property T010;
    @(posedge sclk) ($past(cs_n) && !cs_n) |-> (!cs_n) [*8];
endproperty
assert property (T010)
    else $error("ASSERT", $sformatf("Error T010"));

// TODO: since rx is fixed to B9, will not change wor
// T016: Ensure both RX and done udpate at same clock cycle 
property T016;
    @(edge clk) $rose(done) |-> ($fell(rx_data) || $rose(rx_data));
endproperty
assert property (T016)
    else $error("ASSERT", $sformatf("Error T016"));
