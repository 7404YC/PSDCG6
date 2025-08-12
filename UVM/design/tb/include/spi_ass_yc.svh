// T006: Ensure busy goes high in next clock cycle after start
property T006;
    @(posedge clk) $rose(start) |=> $rose(busy);
endproperty
assert property (T006)
    else $uvm_error("ASSERT", $sformatf("Error T006"));

// T007: Ensure cs_n asserts in next clock cycle after start
property T007;
    @(posedge clk) $rose(start) |=> $rose(cs_n);
endproperty
assert property (T007)
    else $uvm_error("ASSERT", $sformatf("Error T007"));

// T008: Ensure cs_n should not glitch during transfer
property T008;
    @(edge clk) 
endproperty
