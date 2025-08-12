//Assert T001
//T001: Ensure start is ignored if busy is high.
//If busy is high, asserting start should not change the state (no new transfer)
property T001;
    @(posedge clk)
    disable iff (!rst_n)
    (busy && start) |=> state == $past(state);
endproperty

assert property (T001)
    else $error("ASSERT", $sformatf("Error T001"));

//Assert T002
//T002:Ensure no new transaction happens until done pulses
//If a transaction is in progress, another one shouldn't start until `done` is high
property T002;
    @(posedge clk)
    disable iff (!rst_n)
    (start && busy) |=> !$rose(done);
endproperty

assert property (T002)
    else $error("ASSERT", $sformatf("Error T002"));

//Assert T003
//T003: Ensure busy stays high for exactly 8 bits
property T003;
    @(posedge clk)
    disable iff (!rst_n)
    $rose(busy) |=> ##(CLK_DIV*16) $fell(busy);
endproperty

assert property (T003)
    else $error("ASSERT", $sformatf("Error T003"));

//Assert T004
//T004: Verify done is valid for 1 clock cycle (pulse) after the last bit
property T004;
    @(posedge clk)
    disable iff (!rst_n)
    $rose(done) |=> !done;
endproperty

assert property (T004)
    else $error("ASSERT", $sformatf("Error T004"));

//Assert T005
//T005: Ensure busy deasserts in the next clock cycle after done
property T005;
    @(posedge clk)
    disable iff (!rst_n)
    $rose(done) |=> ##1 !busy;
endproperty

assert property (T005)
    else $error("ASSERT", $sformatf("Error T005"));

//Assert T023
property T023;
    @(posedge clk)
    !rst_n |-> (
        sclk == 1'b0 &&
        mosi == 1'b0 &&
        cs_n == 1'b1 &&
        busy == 1'b0 &&
        done == 1'b0
    );
endproperty

assert property (T023)
    else $error("Error T023");
    else $error("ASSERT", $sformatf("Error T023"));
