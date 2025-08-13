wvCreateWindow
wvSetPosition -win $_nWave2 {("G1" 0)}
wvOpenFile -win $_nWave2 \
           {/home/user06/Downloads/PSDCG6/dv_project/uvm_spi/sim/spi_sim.fsdb.bak}
verdiSetActWin -win $_nWave2
verdiWindowResize -win $_Verdi_1 "510" "153" "900" "700"
verdiWindowResize -win $_Verdi_1 "510" "153" "900" "700"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
verdiSetActWin -win $_nWave2
wvGetSignalOpen -win $_nWave2
wvGetSignalSetScope -win $_nWave2 "/spi_tb"
wvGetSignalSetScope -win $_nWave2 "/spi_tb/\\spi_seq::body "
wvGetSignalSetScope -win $_nWave2 "/spi_tb/dut"
wvSetPosition -win $_nWave2 {("G1" 16)}
wvSetPosition -win $_nWave2 {("G1" 16)}
wvAddSignal -win $_nWave2 -clear
wvAddSignal -win $_nWave2 -group {"G1" \
{/spi_tb/dut/bit_cnt\[2:0\]} \
{/spi_tb/dut/busy} \
{/spi_tb/dut/clk} \
{/spi_tb/dut/clk_cnt\[3:0\]} \
{/spi_tb/dut/cs_n} \
{/spi_tb/dut/done} \
{/spi_tb/dut/miso} \
{/spi_tb/dut/mosi} \
{/spi_tb/dut/rst_n} \
{/spi_tb/dut/rx_data\[7:0\]} \
{/spi_tb/dut/rx_reg\[7:0\]} \
{/spi_tb/dut/sclk} \
{/spi_tb/dut/start} \
{/spi_tb/dut/state\[31:0\]} \
{/spi_tb/dut/tx_data\[7:0\]} \
{/spi_tb/dut/tx_reg\[7:0\]} \
}
wvAddSignal -win $_nWave2 -group {"G2" \
}
wvSelectSignal -win $_nWave2 {( "G1" 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 )} \
           
wvSetPosition -win $_nWave2 {("G1" 16)}
wvSetPosition -win $_nWave2 {("G1" 16)}
wvSetPosition -win $_nWave2 {("G1" 16)}
wvAddSignal -win $_nWave2 -clear
wvAddSignal -win $_nWave2 -group {"G1" \
{/spi_tb/dut/bit_cnt\[2:0\]} \
{/spi_tb/dut/busy} \
{/spi_tb/dut/clk} \
{/spi_tb/dut/clk_cnt\[3:0\]} \
{/spi_tb/dut/cs_n} \
{/spi_tb/dut/done} \
{/spi_tb/dut/miso} \
{/spi_tb/dut/mosi} \
{/spi_tb/dut/rst_n} \
{/spi_tb/dut/rx_data\[7:0\]} \
{/spi_tb/dut/rx_reg\[7:0\]} \
{/spi_tb/dut/sclk} \
{/spi_tb/dut/start} \
{/spi_tb/dut/state\[31:0\]} \
{/spi_tb/dut/tx_data\[7:0\]} \
{/spi_tb/dut/tx_reg\[7:0\]} \
}
wvAddSignal -win $_nWave2 -group {"G2" \
}
wvSelectSignal -win $_nWave2 {( "G1" 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 )} \
           
wvSetPosition -win $_nWave2 {("G1" 16)}
wvGetSignalClose -win $_nWave2
wvZoomAll -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 7 )} 
wvSelectSignal -win $_nWave2 {( "G1" 13 )} 
wvSetCursor -win $_nWave2 803274.204743 -snap {("G1" 13)}
wvGetSignalOpen -win $_nWave2
wvGetSignalSetScope -win $_nWave2 "/spi_tb"
wvGetSignalSetScope -win $_nWave2 "/spi_tb/dut"
wvSelectSignal -win $_nWave2 {( "G1" 4 )} 
wvScrollUp -win $_nWave2 3
wvSelectSignal -win $_nWave2 {( "G1" 2 )} 
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 0
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
verdiWindowResize -win $_Verdi_1 "540" "132" "900" "700"
wvSelectSignal -win $_nWave2 {( "G1" 5 )} 
verdiSetActWin -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 5 )} 
wvSelectSignal -win $_nWave2 {( "G1" 6 )} 
wvSetCursor -win $_nWave2 684270.618855 -snap {("G1" 6)}
wvSelectSignal -win $_nWave2 {( "G1" 5 6 )} 
wvSetCursor -win $_nWave2 804626.518219 -snap {("G1" 13)}
verdiWindowResize -win $_Verdi_1 "416" "343" "900" "700"
wvScrollDown -win $_nWave2 4
wvSelectSignal -win $_nWave2 {( "G1" 10 )} 
wvSetCursor -win $_nWave2 685075.937294 -snap {("G1" 6)}
wvZoomAll -win $_nWave2
wvZoomAll -win $_nWave2
wvSetCursor -win $_nWave2 1437846.826516 -snap {("G1" 6)}
wvScrollDown -win $_nWave2 4
wvSelectSignal -win $_nWave2 {( "G1" 15 )} 
wvScrollUp -win $_nWave2 3
wvSelectSignal -win $_nWave2 {( "G1" 11 )} 
wvZoomAll -win $_nWave2
wvSetCursor -win $_nWave2 2208851.382488 -snap {("G1" 6)}
wvSetCursor -win $_nWave2 1429468.049155 -snap {("G1" 11)}
wvSelectSignal -win $_nWave2 {( "G1" 5 )} 
wvSetCursor -win $_nWave2 801771.364452 -snap {("G1" 5)}
wvSelectSignal -win $_nWave2 {( "G1" 12 )} 
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvSelectSignal -win $_nWave2 {( "G1" 13 )} 
verdiSetActWin -win $_nWave2
verdiSetActWin -dock widgetDock_<Inst._Tree>
wvScrollDown -win $_nWave2 0
wvGetSignalOpen -win $_nWave2
wvGetSignalSetScope -win $_nWave2 "/spi_tb"
wvGetSignalSetScope -win $_nWave2 "/spi_tb/dut"
verdiSetActWin -win $_nWave2
wvGetSignalSetScope -win $_nWave2 "/spi_tb"
wvSetPosition -win $_nWave2 {("G1" 18)}
wvSetPosition -win $_nWave2 {("G1" 18)}
wvAddSignal -win $_nWave2 -clear
wvAddSignal -win $_nWave2 -group {"G1" \
{/spi_tb/dut/bit_cnt\[2:0\]} \
{/spi_tb/dut/busy} \
{/spi_tb/dut/clk} \
{/spi_tb/dut/clk_cnt\[3:0\]} \
{/spi_tb/dut/cs_n} \
{/spi_tb/dut/done} \
{/spi_tb/dut/miso} \
{/spi_tb/dut/mosi} \
{/spi_tb/dut/rst_n} \
{/spi_tb/dut/rx_data\[7:0\]} \
{/spi_tb/dut/rx_reg\[7:0\]} \
{/spi_tb/dut/sclk} \
{/spi_tb/dut/start} \
{/spi_tb/dut/state\[31:0\]} \
{/spi_tb/dut/tx_data\[7:0\]} \
{/spi_tb/dut/tx_reg\[7:0\]} \
{/spi_tb/slave_rx_data\[7:0\]} \
{/spi_tb/slave_tx_data\[7:0\]} \
}
wvAddSignal -win $_nWave2 -group {"G2" \
}
wvSelectSignal -win $_nWave2 {( "G1" 17 18 )} 
wvSetPosition -win $_nWave2 {("G1" 18)}
wvSetPosition -win $_nWave2 {("G1" 18)}
wvSetPosition -win $_nWave2 {("G1" 18)}
wvAddSignal -win $_nWave2 -clear
wvAddSignal -win $_nWave2 -group {"G1" \
{/spi_tb/dut/bit_cnt\[2:0\]} \
{/spi_tb/dut/busy} \
{/spi_tb/dut/clk} \
{/spi_tb/dut/clk_cnt\[3:0\]} \
{/spi_tb/dut/cs_n} \
{/spi_tb/dut/done} \
{/spi_tb/dut/miso} \
{/spi_tb/dut/mosi} \
{/spi_tb/dut/rst_n} \
{/spi_tb/dut/rx_data\[7:0\]} \
{/spi_tb/dut/rx_reg\[7:0\]} \
{/spi_tb/dut/sclk} \
{/spi_tb/dut/start} \
{/spi_tb/dut/state\[31:0\]} \
{/spi_tb/dut/tx_data\[7:0\]} \
{/spi_tb/dut/tx_reg\[7:0\]} \
{/spi_tb/slave_rx_data\[7:0\]} \
{/spi_tb/slave_tx_data\[7:0\]} \
}
wvAddSignal -win $_nWave2 -group {"G2" \
}
wvSelectSignal -win $_nWave2 {( "G1" 17 18 )} 
wvSetPosition -win $_nWave2 {("G1" 18)}
wvGetSignalClose -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 6 )} 
wvSetCursor -win $_nWave2 682712.047478 -snap {("G1" 6)}
verdiWindowResize -win $_Verdi_1 "575" "272" "900" "700"
wvSetCursor -win $_nWave2 318344.211551 -snap {("G1" 8)}
wvSelectSignal -win $_nWave2 {( "G1" 7 )} 
wvScrollDown -win $_nWave2 7
wvSelectSignal -win $_nWave2 {( "G1" 18 )} 
wvSetCursor -win $_nWave2 328030.413790 -snap {("G1" 9)}
wvSetCursor -win $_nWave2 681621.639045 -snap {("G1" 18)}
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvSelectSignal -win $_nWave2 {( "G1" 6 )} 
