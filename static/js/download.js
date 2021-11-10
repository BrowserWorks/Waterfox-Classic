$(function () {
    GetLatestWinReleaseInfo();
    GetLatestLinuxReleaseInfo();
    GetLatestmacOSReleaseInfo();
});

function GetLatestWinReleaseInfo() {
    $.getJSON("https://api.github.com/repos/WaterfoxCo/Waterfox-Classic/releases/latest").done(function (release) {
        var asset = release.assets.find(asset => asset.name.endsWith(".exe"));
        $(".win-btn").attr("href", asset.browser_download_url);
    });
}
function GetLatestLinuxReleaseInfo() {
    $.getJSON("https://api.github.com/repos/WaterfoxCo/Waterfox-Classic/releases/latest").done(function (release) {
        var asset = release.assets.find(asset => asset.name.endsWith(".bz2"));
        $(".linux-btn").attr("href", asset.browser_download_url);
    });
}
function GetLatestmacOSReleaseInfo() {
    $.getJSON("https://api.github.com/repos/WaterfoxCo/Waterfox-Classic/releases/latest").done(function (release) {
        var asset = release.assets.find(asset => asset.name.endsWith(".dmg"));
        $(".mac-btn").attr("href", asset.browser_download_url);
    });
}
