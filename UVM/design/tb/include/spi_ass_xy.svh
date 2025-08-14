//Assert T003
//T003: Ensure busy stays high for exactly 8 bits
property T003;
    @(posedge clk)
    disable iff (!rst_n)
    $rose(busy) |-> ##(CLK_DIV*8+1) $fell(busy);
endproperty

ASSERT_T003: assert property (T003)
    else $error("ASSERT ", $sformatf("Error T003"));

//Assert T004
//T004: Verify done is valid for 1 clock cycle (pulse) after the last bit
property T004;
    @(posedge clk)
    disable iff (!rst_n)
    $rose(done) |=> !done;
endproperty

ASSERT_T004: assert property (T004)
    else $error("ASSERT ", $sformatf("Error T004"));

//Assert T005
//T005: Ensure busy deasserts in the next clock cycle after done
property T005;
    @(posedge clk)
    disable iff (!rst_n)
    $rose(done) |-> ##1 !busy;
endproperty

ASSERT_T005: assert property (T005)
    else $error("ASSERT ", $sformatf("Error T005"));

//Assert T017
//T017: Verify sclk frequency matches to the clock divider configuration.
property T017 (int clk_period);
		realtime current_time;
		disable iff(!rst_n || state == 0)
		(('1,current_time=$realtime) |=>(clk_period==$realtime-current_time));
endproperty
ASSERT_T017: assert property (@(posedge sclk) T017 (10*CLK_DIV))
    else $error("ASSERT ", $sformatf("Error T017"));

//Assert T019
//T019: Ensure sclk don't change outside of transfers
property T019;
    @(posedge clk)
    disable iff (!rst_n)
    !busy |=> (
        $stable(sclk)
    );
endproperty

ASSERT_T019: assert property (T019)
    else $error("ASSERT ", $sformatf("Error T019"));

//Assert T023
property T023;
    @(posedge clk)
    !rst_n |-> (
        sclk == 1'b0 &&
        cs_n == 1'b1 &&
        busy == 1'b0 &&
        done == 1'b0
    );
endproperty

ASSERT_T023: assert property (T023)
    else $error("ASSERT ", $sformatf("Error T023"));
