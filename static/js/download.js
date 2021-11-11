$(function () {
    GetLatestWinReleaseInfo();
    GetLatestLinuxReleaseInfo();
    GetLatestmacOSReleaseInfo();
});

function GetLatestWinReleaseInfo() {
    $.getJSON("https://api.github.com/repos/WaterfoxCo/Waterfox-Classic/releases/latest").done(function (release) {
        var asset = release.assets.find(asset => asset.name.endsWith(".exe"));
        var releaseInfo = "Version: " + release.tag_name +
        " Released: " + moment(asset.updated_at).format("YYYY-MM-DD");
        $(".win-btn").attr("href", asset.browser_download_url);
        $(".releaseinfo").append(releaseInfo);
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
