function init(){    
$("div.proof").click(function()
{
    test=$(this).css("background-color")=='rgb(255, 255, 238)'
    $("div.proof").css("max-height","0.8em");
    $("div.proof").css("background-color",'rgb(255, 255, 238)');
    /*if($(this).css("background-color")=='rgb(255, 255, 238)')*/
    if(test==true)
    {
        $(this).css("max-height","1000em");
        $(this).css("background-color","#FFEECC");
    }
    else{
        $(this).css("max-height","0.8em");
        $(this).css("background-color","#FFFFEE");
    }
});
}